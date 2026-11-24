-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_third_idempotent_mul_vector
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.third_idempotent_mul_vector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:02.460326+00:00
-- url     : https://prove2.me/theorems/82c7fb11-85a3-4e11-9063-9a79dda3aaad
-- title:
--   Fr: third idempotent mul vector
-- statement:
--   The Fr construction uses the third idempotent mul vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L213-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L213-L213

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

theorem PositivityTheory.ThKEnd.Cusp.Fr.third_idempotent_mul_vector : e3 c J u u' * u = 0 := by sorry
