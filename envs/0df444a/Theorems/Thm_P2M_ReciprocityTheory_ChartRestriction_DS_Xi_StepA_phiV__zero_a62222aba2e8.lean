-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__zero_a62222aba2e8
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__zero_a62222aba2e8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:54.756339+00:00
-- url     : https://prove2.me/theorems/5f72ad8f-6a7b-4f0d-a84c-dfd4ba1fa77b
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  zero a62222aba2e8: P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  zero a62222aba2e8
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  zero a62222aba2e8 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  zero a62222aba2e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GoodRowsProjectorApplyEqSum.lean#L275-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GoodRowsProjectorApplyEqSum.lean#L275-L276

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__zero_a62222aba2e8 : phiV' k (1 + r') 0 = e0 k r' := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«StepA».«phiV'_zero» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__zero_a62222aba2e8
