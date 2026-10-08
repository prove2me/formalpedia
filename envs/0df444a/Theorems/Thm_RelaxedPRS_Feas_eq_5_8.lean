-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_eq_5_8
-- name    : RelaxedPRS.Feas.eq_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:28.896979+00:00
-- url     : https://prove2.me/theorems/ecf48522-b616-433f-abed-6aa6da216abd
-- title:
--   (5.8), proof of Theorem 5.1, p. 19 — d²_{C_f}(z) ≤ 2 max{c₁², 1}(d²_{C_g}(z) + d²_{C_f}(refl_{γ_g g}(z)))
-- statement:
--   Let $C_f,C_g$ be closed convex subsets of a real Hilbert space $\mathcal H$ with $C_f\cap C_g\neq\emptyset$, let $\gamma_g>0$, $P_g=\mathbf{prox}_{\gamma_g d^2_{C_g}}$, $z\in\mathcal H$, $r=\mathbf{refl}_{\gamma_g g}(z)=2P_g(z)-z$ and $c_1=4\gamma_g/(2\gamma_g+1)$. Then
--   $$
--   d^2_{C_f}(z)\le\big(\|z-r\|+d_{C_f}(r)\big)^2
--   \quad\text{and}\quad
--   d^2_{C_f}(z)\le 2\max\{c_1^2,1\}\big(d^2_{C_g}(z)+d^2_{C_f}(r)\big). \tag{5.8}
--   $$
--
--   This bounds the distance of the current point to $C_f$, which the PRS step never measures directly, by the two distances that appear in the fundamental inequality (5.2).
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 19, proof of Theorem 5.1, (5.8)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proof of Theorem 5.1, (5.8), p. 19: with `c₁ = 4γ_g/(2γ_g+1)`,
`d²_{C_f}(z) ≤ (‖z − refl_{γ_g g}(z)‖ + d_{C_f}(refl_{γ_g g}(z)))²
  ≤ 2 max{c₁², 1}(d²_{C_g}(z) + d²_{C_f}(refl_{γ_g g}(z)))`. -/
theorem eq_5_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Cf Cg : Set H) (hCfc : IsClosed Cf) (hCfv : Convex ℝ Cf) (hCgc : IsClosed Cg)
    (hCgv : Convex ℝ Cg) (hne : (Cf ∩ Cg).Nonempty)
    (γg : ℝ) (hγg : 0 < γg) (Pg : H → H) (hPg : IsProx γg (dsq Cg) Pg) (z : H) :
    Metric.infDist z Cf ^ 2 ≤ (‖z - RelaxedPRS.StrongCvx.refl Pg z‖ + Metric.infDist (RelaxedPRS.StrongCvx.refl Pg z) Cf) ^ 2 ∧
      Metric.infDist z Cf ^ 2 ≤
        2 * max ((4 * γg / (2 * γg + 1)) ^ 2) 1 *
          (Metric.infDist z Cg ^ 2 + Metric.infDist (RelaxedPRS.StrongCvx.refl Pg z) Cf ^ 2) := by sorry

end RelaxedPRS.Feas
