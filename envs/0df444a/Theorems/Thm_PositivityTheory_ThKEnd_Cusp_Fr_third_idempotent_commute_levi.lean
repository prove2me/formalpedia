-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_third_idempotent_commute_levi
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.third_idempotent_commute_levi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:09.556805+00:00
-- url     : https://prove2.me/theorems/628e7aea-6007-48ac-ba4a-b87dbaa67c61
-- title:
--   Fr: third idempotent commute levi
-- statement:
--   The Fr construction uses the third idempotent commute levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L129-L130

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Cusp
open Matrix
variable {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {c : R →+* R}
  {J x y x' y' : Matrix n n R} {u u' : Matrix n ι R}
open PositivityTheory.ThKEnd.Cusp.Fr
variable (h : Fr c J u u')
include h

theorem PositivityTheory.ThKEnd.Cusp.Fr.third_idempotent_commute_levi (g g' : Matrix ι ι R) : e3 c J u u' * lv c J u u' g g' = lv c J u u' g g' * e3 c J u u' := by sorry
