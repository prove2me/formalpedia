-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__li_6fbc45786d0f
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__li_6fbc45786d0f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:19:15.99075+00:00
-- url     : https://prove2.me/theorems/0dd8bb3c-7038-4870-bcbb-cdfcc3f71f2c
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  li 6fbc45786d0f: P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  li 6fbc45786d0f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  li 6fbc45786d0f construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Step A ea phi V  li 6fbc45786d0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L473-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LastBasisZero.lean#L473-L496

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__li_6fbc45786d0f {k r : ℕ} (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«StepA».«ea_phiV'_li» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__li_6fbc45786d0f
