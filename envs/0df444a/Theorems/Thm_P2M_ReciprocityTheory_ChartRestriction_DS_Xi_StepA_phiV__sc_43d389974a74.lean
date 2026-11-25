-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__sc_43d389974a74
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__sc_43d389974a74
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:52.079789+00:00
-- url     : https://prove2.me/theorems/790b880a-fea6-4404-912b-8ee5834d2187
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  sc 43d389974a74: P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  sc 43d389974a74
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  sc 43d389974a74 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Step A phi V  sc 43d389974a74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GoodRowsProjectorApplyEqSum.lean#L278-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GoodRowsProjectorApplyEqSum.lean#L278-L279

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__sc_43d389974a74 (a : Fin (r' + 1)) : phiV' k (1 + r') (sc r' a) = liftVec k 1 r' (phiV' k r' a) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«StepA».«phiV'_sc» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_phiV__sc_43d389974a74
