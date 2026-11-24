-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThKEnd_Cusp_Fr_vv__17029c23a82f
-- name    : P2M_PositivityTheory_ThKEnd_Cusp_Fr_vv__17029c23a82f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:54.854844+00:00
-- url     : https://prove2.me/theorems/097cf40f-8952-4e20-afc7-1efb3c6c9e1a
-- title:
--   P2 M Positivity Theory Th KEnd Cusp Fr vv  17029c23a82f: P2 M Positivity Theory Th KEnd Cusp Fr vv  17029c23a82f
-- statement:
--   The P2 M Positivity Theory Th KEnd Cusp Fr vv  17029c23a82f construction uses the P2 M Positivity Theory Th KEnd Cusp Fr vv  17029c23a82f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L58-L60

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

theorem P2M_PositivityTheory_ThKEnd_Cusp_Fr_vv__17029c23a82f : row c J u' * u' = 0 := by sorry

alias «PositivityTheory».«ThKEnd».«Cusp».«Fr».«vv'» := P2M_PositivityTheory_ThKEnd_Cusp_Fr_vv__17029c23a82f
