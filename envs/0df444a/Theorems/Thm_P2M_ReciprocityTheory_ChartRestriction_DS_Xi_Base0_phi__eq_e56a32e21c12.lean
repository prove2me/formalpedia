-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__eq_e56a32e21c12
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__eq_e56a32e21c12
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:53:16.578529+00:00
-- url     : https://prove2.me/theorems/684c964c-43eb-40d7-8650-67d91d3bc28b
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  eq e56a32e21c12: P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  eq e56a32e21c12
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  eq e56a32e21c12 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  eq e56a32e21c12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L52-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__eq_e56a32e21c12 (hk : 1 ≤ k) :
    phiV' k 0 0 = ((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) - bvec (iK k)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«Base0».«phi'_eq» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__eq_e56a32e21c12
