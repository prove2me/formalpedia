-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThKEnd_Cusp_Fr_uv__9cf1dc9daa1c
-- name    : P2M_PositivityTheory_ThKEnd_Cusp_Fr_uv__9cf1dc9daa1c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:07.231889+00:00
-- url     : https://prove2.me/theorems/433b6bcf-8e79-4523-b7f3-61c26c66e90d
-- title:
--   P2 M Positivity Theory Th KEnd Cusp Fr uv  9cf1dc9daa1c: P2 M Positivity Theory Th KEnd Cusp Fr uv  9cf1dc9daa1c
-- statement:
--   The P2 M Positivity Theory Th KEnd Cusp Fr uv  9cf1dc9daa1c construction uses the P2 M Positivity Theory Th KEnd Cusp Fr uv  9cf1dc9daa1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L66-L68

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

theorem P2M_PositivityTheory_ThKEnd_Cusp_Fr_uv__9cf1dc9daa1c : row c J u * u' = -1 := by sorry

alias «PositivityTheory».«ThKEnd».«Cusp».«Fr».«uv'» := P2M_PositivityTheory_ThKEnd_Cusp_Fr_uv__9cf1dc9daa1c
