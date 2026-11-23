-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_integrable_of_decayVG
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.integrable_of_decayVG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:21.705942+00:00
-- url     : https://prove2.me/theorems/eee4c41b-c45a-4bef-b3ce-0bcf3a9995d3
-- title:
--   S7: integrable of decay VG
-- statement:
--   The S7 construction uses the integrable of decay VG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L128-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean#L128-L241

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.integrable_of_decayVG {E : Type*} [NormedAddCommGroup E] (ε : Fin n → Bool) (s : Bool)
    (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (f : UJ ε → E) (hf : AEStronglyMeasurable f ν) (M : ℝ)
    (hM : ∀ g, hs (toM g) ≤ (n : ℝ) * Real.exp 2 + 1 → ‖f g‖ ≤ M) (a : ℝ)
    (ha : ((2 * (n * Fintype.card (SgIxV ε s)) : ℕ) : ℝ) < a)
    (hdec : ∀ g, (n : ℝ) * Real.exp 2 + 1 < hs (toM g) →
      ∃ t : ℝ, hs (toM g) ≤ n * Real.exp (2 * t) ∧ ‖f g‖ ≤ M * Real.exp (-(a * t))) :
    Integrable f ν := by sorry
