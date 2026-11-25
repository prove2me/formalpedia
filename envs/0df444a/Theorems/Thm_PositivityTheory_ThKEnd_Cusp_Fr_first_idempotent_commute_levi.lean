-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_first_idempotent_commute_levi
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.first_idempotent_commute_levi
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:33.32805+00:00
-- url     : https://prove2.me/theorems/c666e04f-8d05-4e54-a500-d7d037923c69
-- title:
--   Fr: first idempotent commute levi
-- statement:
--   The Fr construction uses the first idempotent commute levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L126-L127

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

theorem PositivityTheory.ThKEnd.Cusp.Fr.first_idempotent_commute_levi (g g' : Matrix ι ι R) : e1 c J u u' * lv c J u u' g g' = lv c J u u' g g' * e1 c J u u' := by sorry
