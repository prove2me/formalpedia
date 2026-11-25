-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_incr
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.incr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:11.6986+00:00
-- url     : https://prove2.me/theorems/000fb67b-9049-4f33-a40f-392835f9e37f
-- title:
--   Unit A: incr
-- statement:
--   The Unit A construction uses the incr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L163-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L163-L201

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

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.incr {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' b : G → ℂ}
    (ha' : Continuous a') (hb : Continuous b)
    (haL : MemLp a 2 μ) (ha'L : MemLp a' 2 μ) (hbL : MemLp b 2 μ)
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => pr μ (fun x => a' (x * φ s)) b) MeasureTheory.volume 0 t ∧
    pr μ (fun x => a (x * φ t)) b - pr μ a b =
      ∫ s in (0:ℝ)..t, pr μ (fun x => a' (x * φ s)) b := by sorry
