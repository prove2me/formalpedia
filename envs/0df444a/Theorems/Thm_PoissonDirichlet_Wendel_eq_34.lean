-- Prove2me | Theorems.Thm_PoissonDirichlet_Wendel_eq_34
-- name    : PoissonDirichlet.Wendel.eq_34
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:38.400539+00:00
-- url     : https://prove2.me/theorems/dd0e90dc-2cde-4b48-bc3e-cc17b7e130dc
-- title:
--   (34), p. 863 — ψ_α(λ) = Γ(1 − α)λ^α + φ_α(λ)
-- statement:
--   Let $0<\alpha<1$ and let $\phi_\alpha$, $\psi_\alpha$ be defined by (33) and the first expression of (34). Then for every $\lambda\ge0$,
--   $$\psi_\alpha(\lambda)=\Gamma(1-\alpha)\lambda^\alpha+\phi_\alpha(\lambda).$$
--
--   This identity, the second equality in (34), links the two Laplace exponents appearing in Proposition 11 to the Laplace exponent $\Gamma(1-\alpha)\lambda^\alpha$ of a stable($\alpha$) subordinator.
--
--   **Formalization Note** At $\lambda=0$ the identity reads $1=0+1$, with $0^\alpha=0$ for $\alpha>0$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 863, (34), second equality

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- (34), second equality, p. 863: for 0 < α < 1 and λ ≥ 0,
`ψ_α(λ) = Γ(1 - α) λ^α + φ_α(λ)`. -/
theorem eq_34 (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (l : ℝ) (hl : 0 ≤ l) :
    psi α l = Real.Gamma (1 - α) * l ^ α + phi α l := by sorry

end PoissonDirichlet.Wendel
