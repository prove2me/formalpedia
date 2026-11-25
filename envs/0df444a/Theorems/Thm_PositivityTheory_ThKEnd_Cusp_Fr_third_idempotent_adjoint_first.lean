-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_third_idempotent_adjoint_first
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.third_idempotent_adjoint_first
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:09.252442+00:00
-- url     : https://prove2.me/theorems/bb9fb842-76a5-4263-b3f8-195322036583
-- title:
--   Fr: third idempotent adjoint first
-- statement:
--   The Fr construction uses the third idempotent adjoint first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L153-L155

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

theorem PositivityTheory.ThKEnd.Cusp.Fr.third_idempotent_adjoint_first : Adj c J (e3 c J u u') (e1 c J u u') := by sorry
