-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_prop_5_2
-- name    : RelaxedPRS.Feas.prop_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:50.007991+00:00
-- url     : https://prove2.me/theorems/7bc59ed3-6239-4bff-90ae-7691895d96c8
-- title:
--   Proposition 5.2 (= C.3), p. 18 — 8λ(γ_f d²_{C_f}(x_f) + γ_g d²_{C_g}(x_g)) ≤ ‖z − x*‖² − ‖z⁺ − x*‖² + (1 − 1/λ)‖z⁺ − z‖²
-- statement:
--   Let $C_f,C_g$ be closed convex subsets of a real Hilbert space $\mathcal H$ with $C_f\cap C_g\ne\emptyset$, let $\gamma_f,\gamma_g>0$, and let $P_f=\mathbf{prox}_{\gamma_f d^2_{C_f}}$, $P_g=\mathbf{prox}_{\gamma_g d^2_{C_g}}$. For $z\in\mathcal H$ put $x_g=P_g(z)$, $x_f=P_f(2x_g-z)$, and for $\lambda>0$ let
--   $$
--   z^+=(T^{\gamma_f,\gamma_g}_{\mathrm{PRS}})_\lambda(z)=(1-\lambda)z+\lambda\,\mathbf{refl}_{\gamma_f f}\big(\mathbf{refl}_{\gamma_g g}(z)\big).
--   $$
--   Then for every $x^*\in C_f\cap C_g$,
--   $$
--   8\lambda\big(\gamma_f\,d^2_{C_f}(x_f)+\gamma_g\,d^2_{C_g}(x_g)\big)\le\|z-x^*\|^2-\|z^+-x^*\|^2+\Big(1-\frac1\lambda\Big)\|z^+-z\|^2. \tag{5.2}
--   $$
--
--   This is the paper's fundamental inequality specialised to squared distance functions; it is the only analytic input of the linear convergence proof of Theorem 5.1.
--
--   **Formalization Note** Prox maps are given by the published `IsProx` predicate; $z^+$ is written with the averaged operator `relaxOp (TPRS Pf Pg) λ z`. Only $\lambda>0$ is assumed, as on the page.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 18, Proposition 5.2, (5.2); restated p. 36 as Proposition C.3, (C.3)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proposition 5.2 (= Proposition C.3), p. 18: with `z⁺ = (T^{γ_f,γ_g}_PRS)_λ(z)`, for every
`x* ∈ C_f ∩ C_g`,
`8λ(γ_f d²_{C_f}(x_f) + γ_g d²_{C_g}(x_g)) ≤ ‖z − x*‖² − ‖z⁺ − x*‖² + (1 − 1/λ)‖z⁺ − z‖²`. -/
theorem prop_5_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Cf Cg : Set H) (hCfc : IsClosed Cf) (hCfv : Convex ℝ Cf) (hCgc : IsClosed Cg)
    (hCgv : Convex ℝ Cg) (hne : (Cf ∩ Cg).Nonempty)
    (γf γg : ℝ) (hγf : 0 < γf) (hγg : 0 < γg) (Pf Pg : H → H)
    (hPf : IsProx γf (dsq Cf) Pf) (hPg : IsProx γg (dsq Cg) Pg)
    (t : ℝ) (ht : 0 < t) (z : H) :
    ∀ x ∈ Cf ∩ Cg,
      8 * t * (γf * Metric.infDist (RelaxedPRS.StrongCvx.xf Pf Pg z) Cf ^ 2 + γg * Metric.infDist (RelaxedPRS.BestIter.xg Pg z) Cg ^ 2) ≤
        ‖z - x‖ ^ 2 - ‖relaxOp (RelaxedPRS.StrongCvx.TPRS Pf Pg) t z - x‖ ^ 2 +
          (1 - 1 / t) * ‖relaxOp (RelaxedPRS.StrongCvx.TPRS Pf Pg) t z - z‖ ^ 2 := by sorry

end RelaxedPRS.Feas
