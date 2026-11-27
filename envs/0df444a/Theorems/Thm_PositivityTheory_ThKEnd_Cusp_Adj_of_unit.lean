-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_of_unit
-- name    : PositivityTheory.ThKEnd.Cusp.Adj.of_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:59:32.728702+00:00
-- url     : https://prove2.me/theorems/cbc6f3bb-e187-4a0c-bd7e-92da79d22744
-- title:
--   Adj: of unit
-- statement:
--   The Adj construction uses the of unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L30-L33

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

theorem PositivityTheory.ThKEnd.Cusp.Adj.of_unit (h : xᵀ * J * x.map c = J) (e : x * y = 1) : Adj c J x y := by sorry
