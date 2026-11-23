-- Prove2me | Theorems.Thm_PINNConvergence_pinn_elliptic_H1_convergence
-- name    : PINNConvergence.pinn_elliptic_H1_convergence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:10:58.595125+00:00
-- url     : https://prove2.me/theorems/97d29757-e0e0-43d9-bad1-de41da935384
-- title:
--   Theorem 3.4: with exact boundary values, the minimizers converge in $H^1(U)$
-- statement:
--   Under the conditions of Theorem 3.3 as printed (with only $m_r=O(m_b^{d/(d-1)})$), with fixed weights $\lambda_r,\lambda_b>0$, suppose also that every minimizer satisfies the boundary condition: $h_m=g$ on $\partial U$ for all $m$ and all samples. Then with probability $1$ the minimizers converge to the classical solution $u^*$ in $H^1(U)$:
--
--   $$\lim_{m\to\infty}\int_U\Big(|\nabla(h_m-u^*)|^2+|h_m-u^*|^2\Big)\,dx=0.$$
--
--   Learning the boundary data exactly therefore upgrades uniform convergence to convergence in energy.
--
--   **Formalization Note** Both $h_m$ and $u^*$ are $C^1$ on $U$, so the $H^1$ norm is computed with classical gradients. The squared distance takes values in $[0,\infty]$. The reverse rate condition of Theorem 3.3 (as proved) is not needed here: with exact boundary values only the interior residual must converge uniformly, and the one-sided rate suffices for that. Positivity $\lambda_r,\lambda_b>0$ is assumed, as in Theorem 3.3 (as proved). One exponent $\alpha$ serves both Assumption 3.2 ($0<\alpha\le1$) and Assumption 3.3 ($0<\alpha<1$), as the paper uses the single symbol $\alpha$ for both; this excludes the Lipschitz regularization $\alpha=1$ from the elliptic theorems.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Section 3.2, Theorem 3.4, p. 13; proof in Appendix E, p. 26

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem pinn_elliptic_H1_convergence {d : ℕ} (hd : 2 ≤ d) (U : Set (Rd d))
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
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ) (H : ℕ → Smp → Set (Rd d → ℝ))
    (hA2 : NetClassAssumption σ 2 α U (frontier U) (ellipticOp a b c e) id f g lr lb mb XR XB H)
    (h : ℕ → Smp → Rd d → ℝ)
    (hmin : ∀ m : ℕ, 1 ≤ m → ∀ ω, h m ω ∈ H m ω ∧ ∀ h' ∈ H m ω,
      holderRegLoss α U (frontier U) (ellipticOp a b c e) id f g lr lb (lrR m) (lbR m)
          (XR m ω) (XB m ω) (h m ω) ≤
        holderRegLoss α U (frontier U) (ellipticOp a b c e) id f g lr lb (lrR m) (lbR m)
          (XR m ω) (XB m ω) h')
    (hbc : ∀ m : ℕ, 1 ≤ m → ∀ ω, ∀ x ∈ frontier U, h m ω x = g x) :
    ∀ u, IsClassicalSol U a b c e f g u →
      ∀ᵐ ω ∂P, Tendsto (fun m => h1DistSq U (h m ω) u) atTop (𝓝 0) := by sorry

end PINNConvergence
