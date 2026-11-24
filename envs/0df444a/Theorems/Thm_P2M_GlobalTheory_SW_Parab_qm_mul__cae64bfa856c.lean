-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_Parab_qm_mul__cae64bfa856c
-- name    : P2M_GlobalTheory_SW_Parab_qm_mul__cae64bfa856c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:19.229633+00:00
-- url     : https://prove2.me/theorems/73984672-7e0a-4d6d-bf96-4b0b9b683bd8
-- title:
--   P2 M Global Theory SW Parab qm mul  cae64bfa856c: P2 M Global Theory SW Parab qm mul  cae64bfa856c
-- statement:
--   The P2 M Global Theory SW Parab qm mul  cae64bfa856c construction uses the P2 M Global Theory SW Parab qm mul  cae64bfa856c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L145-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
open Matrix Complex
open scoped ComplexConjugate Real

theorem P2M_GlobalTheory_SW_Parab_qm_mul__cae64bfa856c {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (A * B) = _root_.GlobalTheory.SW.qm A * _root_.GlobalTheory.SW.qm B := by sorry

alias «GlobalTheory».«SW».«Parab».«qm_mul'» := P2M_GlobalTheory_SW_Parab_qm_mul__cae64bfa856c
