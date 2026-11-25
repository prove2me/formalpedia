-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_row_mul
-- name    : PositivityTheory.ThKEnd.Cusp.Fr.row_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:03.531632+00:00
-- url     : https://prove2.me/theorems/1a7c8fbc-a14d-4d58-9c03-d21919e54d6b
-- title:
--   Fr: row mul
-- statement:
--   The Fr construction uses the row mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean#L157-L160

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

theorem PositivityTheory.ThKEnd.Cusp.Fr.row_mul {s s' : Matrix n n R} (hs : Adj c J s s') {g : Matrix ι ι R} (e : s' * u = u * g) :
    row c J u * s = (g.map c)ᵀ * row c J u := by sorry
