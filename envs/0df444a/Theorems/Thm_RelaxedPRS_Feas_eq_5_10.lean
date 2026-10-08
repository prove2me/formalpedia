-- Prove2me | Theorems.Thm_RelaxedPRS_Feas_eq_5_10
-- name    : RelaxedPRS.Feas.eq_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:58.461174+00:00
-- url     : https://prove2.me/theorems/33ec0345-657f-48d0-8b39-c2365de953c7
-- title:
--   (5.10), proof of Theorem 5.1, p. 19 — 8λ(…) ≥ 8λ min{γ_g/(2γ_g+1)², γ_f/(2γ_f+1)²}(…) ≥ (8λ min{…}/(2 max{c₁², 1})) max{d²_{C_f}(z), d²_{C_g}(z)}
-- statement:
--   Let $C_f,C_g$ be closed convex subsets of a real Hilbert space $\mathcal H$ with $C_f\cap C_g\neq\emptyset$, let $\gamma_f,\gamma_g>0$, $\lambda>0$, $P_g=\mathbf{prox}_{\gamma_g d^2_{C_g}}$, $z\in\mathcal H$, $r=\mathbf{refl}_{\gamma_g g}(z)$, $c_1=4\gamma_g/(2\gamma_g+1)$ and $m=\min\{\gamma_g/(2\gamma_g+1)^2,\ \gamma_f/(2\gamma_f+1)^2\}$. Then
--   $$
--   8\lambda\Big(\frac{\gamma_f}{(2\gamma_f+1)^2}d^2_{C_f}(r)+\frac{\gamma_g}{(2\gamma_g+1)^2}d^2_{C_g}(z)\Big)
--   \ge 8\lambda m\big(d^2_{C_f}(r)+d^2_{C_g}(z)\big)
--   \ge\frac{8\lambda m}{2\max\{c_1^2,1\}}\max\{d^2_{C_f}(z),d^2_{C_g}(z)\}. \tag{5.10}
--   $$
--
--   Combined with (5.2) and (5.6), this lower-bounds the decrease of $\|z-x^*\|^2$ in one step by the larger of the two distances of $z$ to the sets.
--
--   **Formalization Note** The left-hand side pairs $\gamma_f$ with $d^2_{C_f}(r)$ and $\gamma_g$ with $d^2_{C_g}(z)$, which is what (5.2) and (5.6) produce; the page's (5.9)–(5.10) print the two step sizes swapped. Because $m$ is the minimum over both, the two chained bounds hold for either pairing.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 19, proof of Theorem 5.1, (5.10)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting
open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RelaxedPRS.Feas

/-- Proof of Theorem 5.1, (5.10), p. 19, with the pairing of step sizes and distances that (5.2)
and (5.6) produce (`γ_f` with `d²_{C_f}(refl_{γ_g g}(z))`, `γ_g` with `d²_{C_g}(z)`); the page
prints the two step sizes swapped. With `c₁ = 4γ_g/(2γ_g+1)`:
`8λ(γ_f/(2γ_f+1)² d²_{C_f}(RelaxedPRS.StrongCvx.refl z) + γ_g/(2γ_g+1)² d²_{C_g}(z))
  ≥ 8λ min{γ_g/(2γ_g+1)², γ_f/(2γ_f+1)²}(d²_{C_f}(RelaxedPRS.StrongCvx.refl z) + d²_{C_g}(z))
  ≥ (8λ min{…}/(2 max{c₁², 1})) max{d²_{C_f}(z), d²_{C_g}(z)}`. -/
theorem eq_5_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Cf Cg : Set H) (hCfc : IsClosed Cf) (hCfv : Convex ℝ Cf) (hCgc : IsClosed Cg)
    (hCgv : Convex ℝ Cg) (hne : (Cf ∩ Cg).Nonempty)
    (γf γg : ℝ) (hγf : 0 < γf) (hγg : 0 < γg) (Pg : H → H) (hPg : IsProx γg (dsq Cg) Pg)
    (t : ℝ) (ht : 0 < t) (z : H) :
    8 * t * min (γg / (2 * γg + 1) ^ 2) (γf / (2 * γf + 1) ^ 2) *
        (Metric.infDist (RelaxedPRS.StrongCvx.refl Pg z) Cf ^ 2 + Metric.infDist z Cg ^ 2) ≤
      8 * t * (γf / (2 * γf + 1) ^ 2 * Metric.infDist (RelaxedPRS.StrongCvx.refl Pg z) Cf ^ 2 +
        γg / (2 * γg + 1) ^ 2 * Metric.infDist z Cg ^ 2) ∧
    8 * t * min (γg / (2 * γg + 1) ^ 2) (γf / (2 * γf + 1) ^ 2) /
          (2 * max ((4 * γg / (2 * γg + 1)) ^ 2) 1) *
        max (Metric.infDist z Cf ^ 2) (Metric.infDist z Cg ^ 2) ≤
      8 * t * min (γg / (2 * γg + 1) ^ 2) (γf / (2 * γf + 1) ^ 2) *
        (Metric.infDist (RelaxedPRS.StrongCvx.refl Pg z) Cf ^ 2 + Metric.infDist z Cg ^ 2) := by sorry

end RelaxedPRS.Feas
