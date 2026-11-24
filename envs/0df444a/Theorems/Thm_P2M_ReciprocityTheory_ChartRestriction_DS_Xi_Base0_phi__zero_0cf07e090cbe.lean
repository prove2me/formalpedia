-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__zero_0cf07e090cbe
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__zero_0cf07e090cbe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:52:59.727877+00:00
-- url     : https://prove2.me/theorems/6a0c2c4b-1c2a-4972-98e5-4fd1b7fbc78d
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  zero 0cf07e090cbe: P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  zero 0cf07e090cbe
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  zero 0cf07e090cbe construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Base0 phi  zero 0cf07e090cbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/SphericalFunctionFixedUnitaryEqOne.lean#L73-L76

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__zero_0cf07e090cbe (hk : 1 ≤ k) (i : Fin (2 * 0 + k + 1)) (h1 : i ≠ iW k) (h2 : i ≠ iK k) :
    phiV' k 0 0 i = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«Base0».«phi'_zero» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_phi__zero_0cf07e090cbe
