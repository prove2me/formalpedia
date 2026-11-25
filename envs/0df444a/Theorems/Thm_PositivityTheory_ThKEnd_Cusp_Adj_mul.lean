-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_mul
-- name    : PositivityTheory.ThKEnd.Cusp.Adj.mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:35.061108+00:00
-- url     : https://prove2.me/theorems/3e183fe8-dbcf-43aa-8a17-2e4cd43ed956
-- title:
--   Adj: mul
-- statement:
--   The Adj construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L24-L25

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

theorem PositivityTheory.ThKEnd.Cusp.Adj.mul (h : Adj c J x y) (h' : Adj c J x' y') : Adj c J (x * x') (y' * y) := by sorry
