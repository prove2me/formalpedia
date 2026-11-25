-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KSp_ParNear_toBlocks___one__cee26bb9a5a8
-- name    : P2M_GlobalTheory_KSp_ParNear_toBlocks___one__cee26bb9a5a8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:24.56033+00:00
-- url     : https://prove2.me/theorems/e680e62b-4f7c-47d2-817a-366f790b159f
-- title:
--   P2 M Global Theory KSp Par Near to Blocks   one  cee26bb9a5a8: P2 M Global Theory KSp Par Near to Blocks   one  cee26bb9a5a8
-- statement:
--   The P2 M Global Theory KSp Par Near to Blocks   one  cee26bb9a5a8 construction uses the P2 M Global Theory KSp Par Near to Blocks   one  cee26bb9a5a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatFixedNearOneSiegelParabolic.lean#L20-L21

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

theorem P2M_GlobalTheory_KSp_ParNear_toBlocks___one__cee26bb9a5a8 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by sorry

alias «GlobalTheory».«KSp».«ParNear».«toBlocks₁₁_one'» := P2M_GlobalTheory_KSp_ParNear_toBlocks___one__cee26bb9a5a8
