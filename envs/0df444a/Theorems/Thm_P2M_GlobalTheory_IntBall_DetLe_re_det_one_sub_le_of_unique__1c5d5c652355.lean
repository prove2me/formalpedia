-- Prove2me | Theorems.Thm_P2M_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique__1c5d5c652355
-- name    : P2M_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique__1c5d5c652355
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:14.583115+00:00
-- url     : https://prove2.me/theorems/49051225-2332-48c4-b5ee-78be298ac153
-- title:
--   P2 M Global Theory Int Ball Det Le re det one sub le of unique  1c5d5c652355: P2 M Global Theory Int Ball Det Le re det one sub le of unique  1c5d5c652355
-- statement:
--   The P2 M Global Theory Int Ball Det Le re det one sub le of unique  1c5d5c652355 construction uses the P2 M Global Theory Int Ball Det Le re det one sub le of unique  1c5d5c652355 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetOneSubOffDiagonalBlockGramLeOneBall.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetOneSubOffDiagonalBlockGramLeOneBall.lean#L21-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.DetLe

theorem P2M_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique__1c5d5c652355 {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Unique κ] (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by sorry

alias «GlobalTheory».«IntBall».«DetLe».«re_det_one_sub_le_of_unique'» := P2M_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique__1c5d5c652355
