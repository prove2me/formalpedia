-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_eq_11
-- name    : RetirePartialInfo.Duality.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:50.479309+00:00
-- url     : https://prove2.me/theorems/7b0175ee-79a7-4a04-a175-e0cbadaa4cf2
-- title:
--   (11), p. 11 — Ũ(t, y) = U(t, I(t, y)) − y I(t, y), the supremum attained at I(t, y)
-- statement:
--   Let $U:[0,T]\times(0,\infty)\to\mathbb R$ satisfy Assumption 2.2, let $I(t,\cdot)$ be the inverse of $\partial_cU(t,\cdot)$ and $\tilde U(t,y)=\sup_{c>0}[U(t,c)-yc]$ the convex dual. For every $t\in[0,T]$ and $y>0$: $I(t,y)>0$, the supremum is attained at $c=I(t,y)$, and
--   $$\tilde U(t,y)=U\bigl(t,I(t,y)\bigr)-y\,I(t,y).$$
--
--   This is the Fenchel equality used in every step of the duality argument: $U(t,c)\le\tilde U(t,y)+yc$ for all $c>0$, with equality at the candidate $c=I(t,y)$.
--
--   **Formalization Note.** Stated for a single utility satisfying Assumption 2.2; the paper uses it for $U_1$ and $U_2$.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 11, (11)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **(11)**, p. 11 (Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 11, (11)): "Denote by `Ũ_i` the convex dual functions of the
concave functions `U_i`, `i = 1, 2`. `Ũ_i(t, y) := sup_{c>0}[U_i(t, c) − yc] = U_i(t, I_i(t, y)) − yI_i(t, y)`."

For a utility `U` satisfying Assumption 2.2, every `t ∈ [0, T]` and `y > 0`: `I(t, y) > 0`, the
supremum over `c > 0` of `U(t, c) − yc` is attained at `c = I(t, y)`, and
`Ũ(t, y) = U(t, I(t, y)) − y I(t, y)`.

**Formalization Note.** Posed once for a single `U` satisfying `Assumption22`; it is used for `U_1`
and `U_2`. `I(t, ·)` is `Iinv` (the inverse of `∂_c U(t, ·)`), `Ũ` is `Utilde` (the supremum). -/
theorem eq_11 (p : Params) (U : ℝ → ℝ → ℝ) (hU : Assumption22 p U) (t : ℝ)
    (ht : t ∈ Icc 0 p.T) (y : ℝ) (hy : 0 < y) :
    0 < Iinv U t y ∧
    IsGreatest ((fun c => U t c - y * c) '' Ioi 0) (U t (Iinv U t y) - y * Iinv U t y) ∧
    Utilde U t y = U t (Iinv U t y) - y * Iinv U t y := by sorry

end RetirePartialInfo.Duality
