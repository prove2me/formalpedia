-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KSp_ParNear_toBlocks___mul_of_toBlocks___eq_zero_150fba5587ce
-- name    : P2M_GlobalTheory_KSp_ParNear_toBlocks___mul_of_toBlocks___eq_zero_150fba5587ce
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:53.589582+00:00
-- url     : https://prove2.me/theorems/d7aa5167-95a9-458c-af8f-80fadf9e1613
-- title:
--   P2 M Global Theory KSp Par Near to Blocks   mul of to Blocks   eq zero 150fba5587ce: P2 M Global Theory KSp Par Near to Blocks   mul of to Blocks   eq zero 150fba5587ce
-- statement:
--   The P2 M Global Theory KSp Par Near to Blocks   mul of to Blocks   eq zero 150fba5587ce construction uses the P2 M Global Theory KSp Par Near to Blocks   mul of to Blocks   eq zero 150fba5587ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L15-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarEventuallyEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatFixedNearOneSiegelParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open Filter Topology
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.ParNear
variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem P2M_GlobalTheory_KSp_ParNear_toBlocks___mul_of_toBlocks___eq_zero_150fba5587ce (M N : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (h : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by sorry

alias «GlobalTheory».«KSp».«ParNear».«toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero» := P2M_GlobalTheory_KSp_ParNear_toBlocks___mul_of_toBlocks___eq_zero_150fba5587ce
