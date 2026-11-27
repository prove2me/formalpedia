-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_mid_lv
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.mid_lv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:59:51.41692+00:00
-- url     : https://prove2.me/theorems/654612bc-9aba-457f-8a09-2733e707b1c1
-- title:
--   Fr: mid lv
-- statement:
--   The Fr construction uses the mid lv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L204-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L204-L209

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

theorem PositivityTheory.ThKEnd.Cusp.Fr.mid_lv (g g' k k' : Matrix ι ι R) (s : Matrix n n R) :
    mid c J u u' (lv c J u u' g g' * s * lv c J u u' k k') = mid c J u u' s := by sorry
