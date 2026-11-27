-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_mid_mul
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.mid_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:51.467575+00:00
-- url     : https://prove2.me/theorems/2d37f5b6-cf01-44b8-9dd0-e8f660304e15
-- title:
--   Fr: mid mul
-- statement:
--   The Fr construction uses the mid mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L170-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L170-L194

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

theorem PositivityTheory.ThKEnd.Cusp.Fr.mid_mul {s s' : Matrix n n R} (a : s * e1 c J u u' = e1 c J u u') (b : e3 c J u u' * s' = e3 c J u u') :
    mid c J u u' (s * s') = mid c J u u' s * mid c J u u' s' := by sorry
