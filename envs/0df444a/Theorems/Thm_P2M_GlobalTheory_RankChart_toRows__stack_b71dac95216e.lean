-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
-- name    : P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:04.430649+00:00
-- url     : https://prove2.me/theorems/37905608-e8a9-4b5c-ab6d-4b44da90f61e
-- title:
--   P2 M Global Theory Rank Chart to Rows  stack b71dac95216e: P2 M Global Theory Rank Chart to Rows  stack b71dac95216e
-- statement:
--   The P2 M Global Theory Rank Chart to Rows  stack b71dac95216e construction uses the P2 M Global Theory Rank Chart to Rows  stack b71dac95216e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L38-L39

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

theorem P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e (Y₁ : Matrix R D k) (C : Matrix T R k) : (stack Y₁ C).toRows₁ = Y₁ := by sorry

alias «GlobalTheory».«RankChart».«toRows₁_stack» := P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
