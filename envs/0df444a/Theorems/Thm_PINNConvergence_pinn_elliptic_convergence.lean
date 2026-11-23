-- Prove2me | Theorems.Thm_PINNConvergence_pinn_elliptic_convergence
-- name    : PINNConvergence.pinn_elliptic_convergence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:10:23.033984+00:00
-- url     : https://prove2.me/theorems/0a358b87-7c63-4343-a41b-914179fbb809
-- title:
--   Theorem 3.3 (as proved): PINN minimizers converge uniformly to the solution of the elliptic problem
-- statement:
--   Consider the elliptic Dirichlet problem (3.6), $\mathcal L[u]=f$ in $U$, $u=g$ on $\partial U$, with $\Gamma=\partial U$ and $\mathcal B[h]=h$. Suppose Assumptions 3.1 ($d\ge2$), 3.2 (with $k=2$) and 3.3 hold and $\tilde c=\sum_iD_ib^i+e\le0$ in $U$. Let $\lambda_r,\lambda_b>0$ be fixed and let the activation be smooth. For $m_r=m\ge1$ let $m_b=m_b(m)\ge1$ satisfy
--
--   $$m=O\big(m_b^{d/(d-1)}\big)\quad\text{and}\quad m_b^{d/(d-1)}=O(m),$$
--
--   and let $\lambda^R_m$ satisfy (3.2). The samples are as in Theorem 3.2. Let $h_m\in\mathcal H_m$ minimize the Hölder regularized loss (3.3) over $\mathcal H_m$. Then:
--
--   1. the problem has a classical solution $u^*\in C^2(U)\cap C^0(\overline U)$, unique on $\overline U$;
--   2. with probability $1$, $\displaystyle\lim_{m\to\infty}h_m=u^*$ in $C^0(U)$.
--
--   This is the paper's main consistency result: in the sample limit, minimizers of the regularized PINN loss converge uniformly to the classical solution.
--
--   **Formalization Note** This is the theorem as its proof establishes it. The reverse rate bound $m_b^{d/(d-1)}=O(m)$ is added because the proof goes through Theorem 3.2, whose boundary step needs it. Positivity of $\lambda_r,\lambda_b$ is implicit in the paper. Smoothness of the activation is taken as $C^\infty$. One exponent $\alpha$ serves both Assumption 3.2 ($0<\alpha\le1$) and Assumption 3.3 ($0<\alpha<1$), as the paper uses the single symbol $\alpha$ for both; this excludes the Lipschitz regularization $\alpha=1$ from the elliptic theorems.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Section 3.2, Theorem 3.3, eq. (3.6), p. 13; proof in Appendix D, p. 26

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem pinn_elliptic_convergence {d : ℕ} (hd : 2 ≤ d) (U : Set (Rd d))
    (μr μb : Measure (Rd d)) (cr Cr cb Cb : ℝ)
    (hA1 : DataDistAssumption U (frontier U) μr μb cr Cr cb Cb)
    (α : ℝ) (a : Fin d → Fin d → Rd d → ℝ) (b c : Fin d → Rd d → ℝ) (e f g : Rd d → ℝ)
    (lam0 Lam v : ℝ) (hA3 : EllipticAssumption α U a b c e f g lam0 Lam v)
    (hct : ∀ x ∈ U, ctilde b e x ≤ 0)
    (lr lb : ℝ) (hl : 0 < lr ∧ 0 < lb) (mb : ℕ → ℕ) (hmb : ∀ m, 1 ≤ mb m)
    (hrate : ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ K * (mb m : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)))
    (hrate' : ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → (mb m : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)) ≤ K * m)
    (lrR lbR : ℕ → ℝ) (hR : RegWeightCondition d α lr lb cr Cr cb Cb mb lrR lbR)
    {Smp : Type*} [MeasurableSpace Smp] (P : Measure Smp) [IsProbabilityMeasure P]
    (XR : ∀ m : ℕ, Smp → Fin m → Rd d) (XB : ∀ m : ℕ, Smp → Fin (mb m) → Rd d)
    (hX : IsIIDSampling P μr μb mb XR XB)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ) (H : ℕ → Smp → Set (Rd d → ℝ))
    (hA2 : NetClassAssumption σ 2 α U (frontier U) (ellipticOp a b c e) id f g lr lb mb XR XB H)
    (h : ℕ → Smp → Rd d → ℝ)
    (hmin : ∀ m : ℕ, 1 ≤ m → ∀ ω, h m ω ∈ H m ω ∧ ∀ h' ∈ H m ω,
      holderRegLoss α U (frontier U) (ellipticOp a b c e) id f g lr lb (lrR m) (lbR m)
          (XR m ω) (XB m ω) (h m ω) ≤
        holderRegLoss α U (frontier U) (ellipticOp a b c e) id f g lr lb (lrR m) (lbR m)
          (XR m ω) (XB m ω) h') :
    (∃ u, IsClassicalSol U a b c e f g u ∧
      ∀ w, IsClassicalSol U a b c e f g w → Set.EqOn w u (closure U)) ∧
    ∀ u, IsClassicalSol U a b c e f g u →
      ∀ᵐ ω ∂P, TendstoUniformlyOn (fun m => h m ω) u atTop U := by sorry

end PINNConvergence
