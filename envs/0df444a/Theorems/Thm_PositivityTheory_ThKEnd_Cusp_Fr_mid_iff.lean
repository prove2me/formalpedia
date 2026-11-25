-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_mid_iff
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.mid_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:44.946079+00:00
-- url     : https://prove2.me/theorems/c6534cd4-33dd-4381-b6d8-6076ead077bd
-- title:
--   Fr: mid iff
-- statement:
--   The Fr construction uses the mid iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L234-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L234-L239

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

theorem PositivityTheory.ThKEnd.Cusp.Fr.mid_iff (s : Matrix n n R) :
    mid c J u u' s = 1 ↔ (1 - e1 c J u u' - e3 c J u u') * (s - 1) * (1 - e1 c J u u' - e3 c J u u') = 0 := by sorry
