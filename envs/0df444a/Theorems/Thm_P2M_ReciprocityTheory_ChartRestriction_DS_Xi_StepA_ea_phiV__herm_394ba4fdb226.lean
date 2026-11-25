-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__herm_394ba4fdb226
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__herm_394ba4fdb226
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:59.359565+00:00
-- url     : https://prove2.me/theorems/e4c306b1-a245-498f-90c2-504cfa17bf72
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  herm 394ba4fdb226: P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  herm 394ba4fdb226
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  herm 394ba4fdb226 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  herm 394ba4fdb226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L447-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L447-L471

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__herm_394ba4fdb226 {k r : ℕ} (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«StepA».«ea_phiV'_herm» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__herm_394ba4fdb226
