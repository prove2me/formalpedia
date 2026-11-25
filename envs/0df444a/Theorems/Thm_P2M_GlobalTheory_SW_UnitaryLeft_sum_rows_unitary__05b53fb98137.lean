-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary__05b53fb98137
-- name    : P2M_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary__05b53fb98137
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:38.326771+00:00
-- url     : https://prove2.me/theorems/49a7d432-5168-4f37-b9cc-efdd77823821
-- title:
--   P2 M Global Theory SW Unitary Left sum rows unitary  05b53fb98137: P2 M Global Theory SW Unitary Left sum rows unitary  05b53fb98137
-- statement:
--   The P2 M Global Theory SW Unitary Left sum rows unitary  05b53fb98137 construction uses the P2 M Global Theory SW Unitary Left sum rows unitary  05b53fb98137 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L29-L32

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

theorem P2M_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary__05b53fb98137 {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : Qᵀ * P = 1)
    (U V : Matrix (Fin n) (Fin N) ℂ) :
    ∑ k, (P * U) k ⬝ᵥ (Q * V) k = ∑ k, U k ⬝ᵥ V k := by sorry

alias «GlobalTheory».«SW».«UnitaryLeft».«sum_rows_unitary'» := P2M_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary__05b53fb98137
