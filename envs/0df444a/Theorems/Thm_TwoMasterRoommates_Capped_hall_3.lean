-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_hall_3
-- name    : TwoMasterRoommates.Capped.hall_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:43.515485+00:00
-- url     : https://prove2.me/theorems/adb0ffd8-a1c0-4df3-8af6-4ad7c62b249e
-- title:
--   Eq. (3) — nested-neighborhood Hall criterion
-- statement:
--   Let $S$ and $W$ be finite populations of equal cardinality. Tokens $s\in S$ have ranks $r(s)$ and recipients $w\in W$ have deadlines $d(w)$ in the same linearly ordered set. A bijection assigning each token to a recipient whose deadline is at least its rank exists exactly when
--
--   $$\bigl|\{s:r(s)\le t\}\bigr|\ge\bigl|\{w:d(w)\le t\}\bigr|\qquad\text{for every threshold }t.$$
--
--   No distinctness assumption is imposed on either ranks or deadlines, and the two populations may both be empty. The rank type may itself include a top value, as it does for extended deadlines. This is the exact nested-neighborhood specialization needed for residual token completion.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - encoding: equal-sized finite token and deadline populations → arbitrary finite types of equal cardinality and an Equiv bijection; reason: finite sets and finite types describe the same assignment problem
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 10 (PDF p. 11), equation (3)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Residual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Equation (3), on arbitrary finite equal-sized populations, without distinctness of ranks. -/
theorem hall_3 {S W R : Type} [Fintype S] [Fintype W] [LinearOrder R]
    (r : S → R) (d : W → R) (hcard : Fintype.card S = Fintype.card W) :
    (∃ σ : S ≃ W, ∀ s, r s ≤ d (σ s)) ↔
      ∀ t : R, Fintype.card {w // d w ≤ t} ≤ Fintype.card {s // r s ≤ t} := by sorry

end TwoMasterRoommates.Capped
