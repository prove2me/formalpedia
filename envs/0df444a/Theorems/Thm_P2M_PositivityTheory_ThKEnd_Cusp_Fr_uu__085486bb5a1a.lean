-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThKEnd_Cusp_Fr_uu__085486bb5a1a
-- name    : P2M_PositivityTheory_ThKEnd_Cusp_Fr_uu__085486bb5a1a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:07.465218+00:00
-- url     : https://prove2.me/theorems/b75592d7-e5b1-4693-afd9-9de5d435c542
-- title:
--   P2 M Positivity Theory Th KEnd Cusp Fr uu  085486bb5a1a: P2 M Positivity Theory Th KEnd Cusp Fr uu  085486bb5a1a
-- statement:
--   The P2 M Positivity Theory Th KEnd Cusp Fr uu  085486bb5a1a construction uses the P2 M Positivity Theory Th KEnd Cusp Fr uu  085486bb5a1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L62-L64

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

theorem P2M_PositivityTheory_ThKEnd_Cusp_Fr_uu__085486bb5a1a : row c J u * u = 0 := by sorry

alias «PositivityTheory».«ThKEnd».«Cusp».«Fr».«uu'» := P2M_PositivityTheory_ThKEnd_Cusp_Fr_uu__085486bb5a1a
