-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_sub
-- name    : PositivityTheory.ThKEnd.Cusp.Adj.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:37.370037+00:00
-- url     : https://prove2.me/theorems/9fada533-e510-42cf-8a31-beb31f800d27
-- title:
--   Adj: sub
-- statement:
--   The Adj construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L21-L22

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

theorem PositivityTheory.ThKEnd.Cusp.Adj.sub (h : Adj c J x y) (h' : Adj c J x' y') : Adj c J (x - x') (y - y') := by sorry
