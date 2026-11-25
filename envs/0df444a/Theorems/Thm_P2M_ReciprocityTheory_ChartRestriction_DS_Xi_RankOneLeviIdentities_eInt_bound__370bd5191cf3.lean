-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_eInt_bound__370bd5191cf3
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_eInt_bound__370bd5191cf3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:35.930953+00:00
-- url     : https://prove2.me/theorems/852e7f09-308d-5ce8-b344-0452d28c8bbd
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities e Int bound  370bd5191cf3: P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities e Int bound  370bd5191cf3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities e Int bound  370bd5191cf3 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Rank One Levi Identities e Int bound  370bd5191cf3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergMapContinuous.lean#L151-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergMapContinuous.lean#L151-L215

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ScaleInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergMapContinuous
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
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_eInt_bound__370bd5191cf3 (hGL : GNLower) (hHA : HeisAct) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) ≤
        ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
          gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«RankOneLeviIdentities».«eInt_bound'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_eInt_bound__370bd5191cf3
