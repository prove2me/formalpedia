-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_skew
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.skew
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:44.6398+00:00
-- url     : https://prove2.me/theorems/12a75de8-080e-493b-8d49-87b96764f49e
-- title:
--   Unit A: skew
-- statement:
--   The Unit A construction uses the skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L281-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L281-L326

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
variable [μ.IsMulRightInvariant] [SFinite μ]

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.skew {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) (hφa : ∀ s t, φ (s + t) = φ s * φ t)
    {u u' v v' : G → ℂ} (hu : Continuous u) (hu' : Continuous u') (hv : Continuous v)
    (hv' : Continuous v')
    (huL : MemLp u 2 μ) (hu'L : MemLp u' 2 μ) (hvL : MemLp v 2 μ) (hv'L : MemLp v' 2 μ)
    (hdu : ∀ x t, HasDerivAt (fun s => u (x * φ s)) (u' (x * φ t)) t)
    (hdv : ∀ x t, HasDerivAt (fun s => v (x * φ s)) (v' (x * φ t)) t) :
    pr μ u' v = -pr μ u v' := by sorry
