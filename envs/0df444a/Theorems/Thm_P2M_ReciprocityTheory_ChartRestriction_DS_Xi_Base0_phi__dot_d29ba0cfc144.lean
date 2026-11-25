-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__dot_d29ba0cfc144
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__dot_d29ba0cfc144
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:29.882805+00:00
-- url     : https://prove2.me/theorems/ef210eb7-d87a-4f35-a065-76a5bbfcee4b
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  dot d29ba0cfc144: P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  dot d29ba0cfc144
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  dot d29ba0cfc144 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  dot d29ba0cfc144 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L88-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L88-L100

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__dot_d29ba0cfc144 (hk : 1 ≤ k) : star (phiV' k 0 0) ⬝ᵥ phiV' k 0 0 = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«Base0».«phi'_dot» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__dot_d29ba0cfc144
