-- Prove2me | Theorems.Thm_PINNConvergence_pinn_elliptic_Ck_convergence_fixed_architecture
-- name    : PINNConvergence.pinn_elliptic_Ck_convergence_fixed_architecture
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:11:27.81973+00:00
-- url     : https://prove2.me/theorems/d20f63aa-b2ee-4b62-b6ae-d43912245ce2
-- title:
--   Corollary 3.5: $C^k$ convergence when the solution is a network of fixed architecture
-- statement:
--   Assume the conditions of Theorem 3.3 as printed (with only $m_r=O(m_b^{d/(d-1)})$), with fixed weights $\lambda_r,\lambda_b>0$. Let all classes equal one fixed-architecture network class, $\mathcal H_m=\mathcal H^{NN}_{\vec n}$, and let the activation also satisfy the conditions of Lemma 2.1 for some $k$: $\sigma^{(s)}$ is bounded and Lipschitz for $s\le k$. Suppose the classical solution $u^*$ coincides on $\overline U$ with a network in $\mathcal H^{NN}_{\vec n}$. Suppose also, as in Lemma 2.1, that for each draw of the samples the minimizers $h_m$ have uniformly bounded weights and biases. Then with probability $1$,
--
--   $$h_m\to u^*\quad\text{in }C^k(U).$$
--
--   **Formalization Note** The bounded-weights requirement is part of the conditions of Lemma 2.1, which the corollary invokes. It is stated for each sample sequence. The corollary is stated with the paper's one-sided rate condition. Its printed proof invokes Theorem 3.3, whose proof needs a two-sided rate. Here the bounded weights make the networks equi-Lipschitz, which supplies the boundary equicontinuity directly. Positivity $\lambda_r,\lambda_b>0$ is assumed, as in Theorem 3.3 (as proved). One exponent $\alpha$ serves both Assumption 3.2 ($0<\alpha\le1$) and Assumption 3.3 ($0<\alpha<1$), as the paper uses the single symbol $\alpha$ for both; this excludes the Lipschitz regularization $\alpha=1$ from the elliptic theorems.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Section 3.2, Corollary 3.5, p. 14 (with Lemma 2.1, p. 8)

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem pinn_elliptic_Ck_convergence_fixed_architecture {d : ℕ} (hd : 2 ≤ d) (U : Set (Rd d))
    (μr μb : Measure (Rd d)) (cr Cr cb Cb : ℝ)
    (hA1 : DataDistAssumption U (frontier U) μr μb cr Cr cb Cb)
    (α : ℝ) (a : Fin d → Fin d → Rd d → ℝ) (b c : Fin d → Rd d → ℝ) (e f g : Rd d → ℝ)
    (lam0 Lam v : ℝ) (hA3 : EllipticAssumption α U a b c e f g lam0 Lam v)
    (hct : ∀ x ∈ U, ctilde b e x ≤ 0)
    (lr lb : ℝ) (hl : 0 < lr ∧ 0 < lb) (mb : ℕ → ℕ) (hmb : ∀ m, 1 ≤ mb m)
    (hrate : ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ K * (mb m : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)))
    (lrR lbR : ℕ → ℝ) (hR : RegWeightCondition d α lr lb cr Cr cb Cb mb lrR lbR)
    {Smp : Type*} [MeasurableSpace Smp] (P : Measure Smp) [IsProbabilityMeasure P]
    (XR : ∀ m : ℕ, Smp → Fin m → Rd d) (XB : ∀ m : ℕ, Smp → Fin (mb m) → Rd d)
    (hX : IsIIDSampling P μr μb mb XR XB)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ) (k : ℕ)
    (hσb : ∀ s ≤ k, (∃ M : ℝ, ∀ t, |iteratedDeriv s σ t| ≤ M) ∧
      ∃ K : NNReal, LipschitzWith K (iteratedDeriv s σ))
    (L : ℕ) (n : ℕ → ℕ) (hn : IsArch L n)
    (hA2 : NetClassAssumption σ 2 α U (frontier U) (ellipticOp a b c e) id f g lr lb mb XR XB
      (fun _ _ => nnClass σ d L n))
    (h : ℕ → Smp → Rd d → ℝ)
    (hmin : ∀ m : ℕ, 1 ≤ m → ∀ ω, h m ω ∈ nnClass σ d L n ∧ ∀ h' ∈ nnClass σ d L n,
      holderRegLoss α U (frontier U) (ellipticOp a b c e) id f g lr lb (lrR m) (lbR m)
          (XR m ω) (XB m ω) (h m ω) ≤
        holderRegLoss α U (frontier U) (ellipticOp a b c e) id f g lr lb (lrR m) (lbR m)
          (XR m ω) (XB m ω) h')
    (hbdd : ∀ ω, ∃ (M : ℝ) (W : ℕ → ∀ l, Matrix (Fin (n l)) (Fin (inWidth d n l)) ℝ)
      (bb : ℕ → ∀ l, Fin (n l) → ℝ), ∀ m : ℕ, 1 ≤ m →
        h m ω = nnEval σ d L n (W m) (bb m) ∧ ParamsBounded L (W m) (bb m) M) :
    ∀ u, IsClassicalSol U a b c e f g u →
      (∃ W bb, Set.EqOn (nnEval σ d L n W bb) u (closure U)) →
      ∀ᵐ ω ∂P, TendstoCk k U (fun m => h m ω) u := by sorry

end PINNConvergence
