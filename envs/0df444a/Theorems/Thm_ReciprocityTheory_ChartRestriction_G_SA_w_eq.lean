-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_w_eq
-- name    : ReciprocityTheory.ChartRestriction.G.SA.w_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:35.753487+00:00
-- url     : https://prove2.me/theorems/c2a5aea1-e434-426c-84c8-31cb2f872321
-- title:
--   SA: w eq
-- statement:
--   The SA construction uses the w eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L117-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

theorem ReciprocityTheory.ChartRestriction.G.SA.w_eq {a ai : K} (h : a * ai = 1) :
    !![1, a; 0, 1] * !![1, 0; -ai, 1] * !![1, a; 0, 1] = !![(0 : K), a; -ai, 0] := by sorry
