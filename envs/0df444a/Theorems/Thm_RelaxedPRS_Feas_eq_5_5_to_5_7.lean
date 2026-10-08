-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_eq_5_5_to_5_7
-- name    : RelaxedPRS.Feas.eq_5_5_to_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:50.077712+00:00
-- url     : https://prove2.me/theorems/605cf454-68ff-45a7-8270-f1bbbb4239da
-- title:
--   (5.5)–(5.7), proof of Theorem 5.1, p. 18 — projection identities, d²_{C_g}(x_g) = d²_{C_g}(z)/(2γ_g+1)², ‖z − refl_{γ_g g}(z)‖ = c₁d_{C_g}(z)
-- statement:
--   Let $C_f,C_g$ be closed convex subsets of a real Hilbert space $\mathcal H$ with $C_f\cap C_g\neq\emptyset$ and metric projections $P_{C_f},P_{C_g}$; let $\gamma_f,\gamma_g>0$ and $P_f=\mathbf{prox}_{\gamma_f d^2_{C_f}}$, $P_g=\mathbf{prox}_{\gamma_g d^2_{C_g}}$. For $z\in\mathcal H$ let $x_g=P_g(z)$, $r=\mathbf{refl}_{\gamma_g g}(z)=2x_g-z$ and $x_f=P_f(r)$. Then:
--
--   1. $P_{C_g}(x_g)=P_{C_g}(z)$ and $P_{C_f}(x_f)=P_{C_f}(r)$;
--   2. $\displaystyle d^2_{C_g}(x_g)=\frac{1}{(2\gamma_g+1)^2}d^2_{C_g}(z)$ and $\displaystyle d^2_{C_f}(x_f)=\frac{1}{(2\gamma_f+1)^2}d^2_{C_f}(r)$;  (5.6)
--   3. $\displaystyle\|z-x_g\|=\frac{2\gamma_g}{2\gamma_g+1}d_{C_g}(z)$;
--   4. with $c_1=4\gamma_g/(2\gamma_g+1)$,
--   $$
--   \|z-\mathbf{refl}_{\gamma_g g}(z)\|=2\|z-x_g\|=c_1\,d_{C_g}(z). \tag{5.7}
--   $$
--
--   These identities express one PRS step for the feasibility problem entirely through distances to the two sets.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 18, proof of Theorem 5.1, (5.5)–(5.7)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proof of Theorem 5.1, (5.5)–(5.7), p. 18, for one step with step sizes `γf, γg > 0`:
the projection identities `P_{C_g} x_g = P_{C_g} z` and `P_{C_f} x_f = P_{C_f}(refl_{γ_g g}(z))`,
the distance identities (5.6), `‖z − x_g‖ = (2γ_g/(2γ_g+1)) d_{C_g}(z)`, and (5.7)
`‖z − refl_{γ_g g}(z)‖ = 2‖z − x_g‖ = (4γ_g/(2γ_g+1)) d_{C_g}(z)`. -/
theorem eq_5_5_to_5_7 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Cf Cg : Set H) (hCfc : IsClosed Cf) (hCfv : Convex ℝ Cf) (hCgc : IsClosed Cg)
    (hCgv : Convex ℝ Cg) (hne : (Cf ∩ Cg).Nonempty)
    (PCf PCg : H → H) (hPCf : ∀ x, IsMetricProjection Cf x (PCf x))
    (hPCg : ∀ x, IsMetricProjection Cg x (PCg x))
    (γf γg : ℝ) (hγf : 0 < γf) (hγg : 0 < γg) (Pf Pg : H → H)
    (hPf : IsProx γf (dsq Cf) Pf) (hPg : IsProx γg (dsq Cg) Pg) (z : H) :
    PCg (RelaxedPRS.BestIter.xg Pg z) = PCg z ∧
      PCf (RelaxedPRS.StrongCvx.xf Pf Pg z) = PCf (RelaxedPRS.StrongCvx.refl Pg z) ∧
      Metric.infDist (RelaxedPRS.BestIter.xg Pg z) Cg ^ 2 = 1 / (2 * γg + 1) ^ 2 * Metric.infDist z Cg ^ 2 ∧
      Metric.infDist (RelaxedPRS.StrongCvx.xf Pf Pg z) Cf ^ 2 =
        1 / (2 * γf + 1) ^ 2 * Metric.infDist (RelaxedPRS.StrongCvx.refl Pg z) Cf ^ 2 ∧
      ‖z - RelaxedPRS.BestIter.xg Pg z‖ = 2 * γg / (2 * γg + 1) * Metric.infDist z Cg ∧
      ‖z - RelaxedPRS.StrongCvx.refl Pg z‖ = 2 * ‖z - RelaxedPRS.BestIter.xg Pg z‖ ∧
      ‖z - RelaxedPRS.StrongCvx.refl Pg z‖ = 4 * γg / (2 * γg + 1) * Metric.infDist z Cg := by sorry

end RelaxedPRS.Feas
