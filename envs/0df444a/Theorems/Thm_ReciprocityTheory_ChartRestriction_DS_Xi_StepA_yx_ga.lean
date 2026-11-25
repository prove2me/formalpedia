-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_yx_ga
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.yx_ga
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:25:51.519286+00:00
-- url     : https://prove2.me/theorems/d61ac972-c237-444c-8f7c-2718fd394836
-- title:
--   Step A: yx ga
-- statement:
--   The Step A construction uses the yx ga property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergRankOneDecomposition.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergRankOneDecomposition.lean#L12-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.yx_ga (hB2 : InductiveHeisenbergInputs) (hIW : IW) (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') :
    0 < Ga k (1 + r') 0 (Yx k r' x) ∧ ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x) := by sorry
