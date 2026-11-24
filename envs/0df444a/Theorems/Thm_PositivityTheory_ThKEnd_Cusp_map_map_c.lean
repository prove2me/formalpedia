-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_map_map_c
-- name    : PositivityTheory.ThKEnd.Cusp.map_map_c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:57.147637+00:00
-- url     : https://prove2.me/theorems/9f181004-c805-4054-92e0-56aab24ac1b1
-- title:
--   Cusp: map map c
-- statement:
--   The Cusp construction uses the map map c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L44-L45

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

theorem PositivityTheory.ThKEnd.Cusp.map_map_c {a b : Type} (h : ∀ r, c (c r) = r) (z : Matrix a b R) : (z.map c).map c = z := by sorry
