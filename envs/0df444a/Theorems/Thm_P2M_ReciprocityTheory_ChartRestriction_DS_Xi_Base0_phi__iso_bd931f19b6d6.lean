-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iso_bd931f19b6d6
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iso_bd931f19b6d6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:23.606411+00:00
-- url     : https://prove2.me/theorems/7322f67f-4993-5c45-b9ea-aeb5dd86cd04
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  iso bd931f19b6d6: P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  iso bd931f19b6d6
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  iso bd931f19b6d6 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  iso bd931f19b6d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L119-L121

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iso_bd931f19b6d6 (hk : 1 ≤ k) : herm (Hpk k 0) (phiV' k 0 0) (phiV' k 0 0) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«Base0».«phi'_iso» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__iso_bd931f19b6d6
