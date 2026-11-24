-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
-- name    : P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:00.74159+00:00
-- url     : https://prove2.me/theorems/1b88d264-eead-4572-88a1-0ab0f83a55b9
-- title:
--   P2 M Global Theory Rank Chart to Rows  dil a78c4f6a5c7f: P2 M Global Theory Rank Chart to Rows  dil a78c4f6a5c7f
-- statement:
--   The P2 M Global Theory Rank Chart to Rows  dil a78c4f6a5c7f construction uses the P2 M Global Theory Rank Chart to Rows  dil a78c4f6a5c7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L35-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]

theorem P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f (t : k) (Y : Matrix (R ⊕ T) D k) : (dil t Y).toRows₁ = Y.toRows₁ := by sorry

alias «GlobalTheory».«RankChart».«toRows₁_dil» := P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
