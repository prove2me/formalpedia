-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_ftc
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.ftc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:31.181657+00:00
-- url     : https://prove2.me/theorems/f0ef6288-4dfd-46d9-b09b-5fea710567ed
-- title:
--   Unit A: ftc
-- statement:
--   The Unit A construction uses the ftc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L151-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.ftc {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' : G → ℂ} (ha' : Continuous a')
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) (x : G) (t : ℝ) :
    ∫ s in (0:ℝ)..t, a' (x * φ s) = a (x * φ t) - a x := by sorry
