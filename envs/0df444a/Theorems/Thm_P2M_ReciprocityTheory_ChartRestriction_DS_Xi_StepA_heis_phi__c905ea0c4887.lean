-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_heis_phi__c905ea0c4887
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_heis_phi__c905ea0c4887
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:57:43.653467+00:00
-- url     : https://prove2.me/theorems/659e0e76-266e-4efa-948f-045f69321512
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Step A heis phi  c905ea0c4887: P2 M Reciprocity Theory Chart Restriction DS Xi Step A heis phi  c905ea0c4887
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Step A heis phi  c905ea0c4887 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Step A heis phi  c905ea0c4887 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DetEqMulMinorOfColZero.lean#L174-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DetEqMulMinorOfColZero.lean#L174-L179

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_heis_phi__c905ea0c4887 (hHA : HeisAct) (x : HPar k r') (b : Fin (1 + r' + 1)) :
    heis0 k r' x *ᵥ phiV' k (1 + r') b = phiV' k (1 + r') b -
      herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (liftVec k 1 r' x.1) • phiV' k (1 + r') 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«StepA».«heis_phi'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_heis_phi__c905ea0c4887
