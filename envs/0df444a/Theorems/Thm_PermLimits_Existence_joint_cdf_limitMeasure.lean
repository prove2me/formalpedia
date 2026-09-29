-- Prove2me | Theorems.Thm_PermLimits_Existence_joint_cdf_limitMeasure
-- name    : PermLimits.Existence.joint_cdf_limitMeasure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:58:24.048211+00:00
-- url     : https://prove2.me/theorems/577af9b8-1f98-446b-93a7-01989f18636b
-- title:
--   Eq. (21): joint distribution function of the random point associated with $Z$
-- statement:
--   Let $Z\in\mathcal Z$ and let $(X,Y)$ be the random point associated with $Z$ (pick $X\sim U[0,1]$, then $Y$ with cdf $Z(X,\cdot)$). Then for all $x,y\in[0,1]$,
--   $$F(x,y)=\mathbf P(X\le x,\,Y\le y)=\int_0^x Z(t,y)\,dt .$$
--
--   This identity connects the random point to $Z$; with $x=1$ and condition (b) of Definition 1.3 it shows $Y\sim U[0,1]$.
--
--   **Formalization Note** The law of $(X,Y)$ is the inverse-cdf construction of the definition bundle `LimitMeasure`; this statement is exactly the check that the construction is the source's Definition 2.3. The source reuses $x$ as the integration variable.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 9, Sect. 2.3, Eq. (21)

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitMeasure
open PermLimits.Shared

namespace PermLimits.Existence

open MeasureTheory unitInterval

/-- **Joint distribution function of the random point associated with `Z`** (Hoppen et al.,
*Limits of permutation sequences*, arXiv:1103.5844v2, Sect. 2.3, Eq. (21), p. 9). For a limit
permutation `Z`, the random point `(X, Y)` associated with `Z` (Definition 2.3) satisfies
`F(x, y) = P(X ≤ x, Y ≤ y) = ∫₀ˣ Z(t, y) dt` for all `x, y ∈ [0, 1]`.

**Formalization Note.** `(X, Y)` has law `limitMeasure Z` (the quantile construction), so this
statement is exactly the check that that construction is the paper's Definition 2.3. The paper
reuses `x` as the integration variable; here it is `t`. `∫₀ˣ` is the integral over
`[0, x] = Set.Iic x` in `I`. -/
theorem joint_cdf_limitMeasure (Z : I → I → ℝ) (hZ : IsLimitPerm Z) (x y : I) :
    (limitMeasure Z).real (Set.Iic x ×ˢ Set.Iic y) = ∫ t in Set.Iic x, Z t y := by sorry

end PermLimits.Existence
