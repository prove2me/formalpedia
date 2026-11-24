-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
-- name    : P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:06.164258+00:00
-- url     : https://prove2.me/theorems/ef9ec074-e173-447e-a672-a26c2e117d28
-- title:
--   P2 M Global Theory Rank Chart to Rows  shear d5dffcf9ff0a: P2 M Global Theory Rank Chart to Rows  shear d5dffcf9ff0a
-- statement:
--   The P2 M Global Theory Rank Chart to Rows  shear d5dffcf9ff0a construction uses the P2 M Global Theory Rank Chart to Rows  shear d5dffcf9ff0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L32-L33

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

theorem P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : (shear c Y).toRows₁ = Y.toRows₁ := by sorry

alias «GlobalTheory».«RankChart».«toRows₁_shear» := P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
