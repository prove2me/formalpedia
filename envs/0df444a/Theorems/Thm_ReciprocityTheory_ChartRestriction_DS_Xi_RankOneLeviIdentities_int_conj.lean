-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_int_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.int_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:15.234456+00:00
-- url     : https://prove2.me/theorems/336e418b-2186-4bfa-9ebb-836d376c6dc8
-- title:
--   Rank One Levi Identities: int conj
-- statement:
--   The Rank One Levi Identities construction uses the int conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergMapContinuous.lean#L74-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergMapContinuous.lean#L74-L112

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.int_conj (hCL : HeisConjLev) (hCM : HeisConjLevMeas) (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r')
    (hg : g ∈ GV k r') :
    ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A)) := by sorry
