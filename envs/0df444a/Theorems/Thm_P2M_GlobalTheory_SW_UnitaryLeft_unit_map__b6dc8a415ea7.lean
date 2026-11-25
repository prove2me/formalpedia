-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_UnitaryLeft_unit_map__b6dc8a415ea7
-- name    : P2M_GlobalTheory_SW_UnitaryLeft_unit_map__b6dc8a415ea7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:24.269322+00:00
-- url     : https://prove2.me/theorems/579d9002-99db-5401-ab56-0066f004a3f2
-- title:
--   P2 M Global Theory SW Unitary Left unit map  b6dc8a415ea7: P2 M Global Theory SW Unitary Left unit map  b6dc8a415ea7
-- statement:
--   The P2 M Global Theory SW Unitary Left unit map  b6dc8a415ea7 construction uses the P2 M Global Theory SW Unitary Left unit map  b6dc8a415ea7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L49-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem P2M_GlobalTheory_SW_UnitaryLeft_unit_map__b6dc8a415ea7 {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (τ : E →+* ℂ) :
    (h.map τ)ᵀ * (h.map τ).map conj = 1 := by sorry

alias «GlobalTheory».«SW».«UnitaryLeft».«unit_map'» := P2M_GlobalTheory_SW_UnitaryLeft_unit_map__b6dc8a415ea7
