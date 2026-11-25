-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_degree_piece
-- name    : ReciprocityTheory.AnForm.M.degree_piece
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:33.117262+00:00
-- url     : https://prove2.me/theorems/aeaa1dc7-76a2-40b2-be20-8ed780e5c250
-- title:
--   M: degree piece
-- statement:
--   The M construction uses the degree piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeInt.lean#L111-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeInt.lean#L111-L211

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem ReciprocityTheory.AnForm.M.degree_piece [CompactSpace Y] [T2Space Y] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (P : ChartPartition A)
    (Q : ChartPartition B) {E V : Set X} (hE : MeasurableSet E) (hEV : E ⊆ V) (hV : IsOpen V)
    {k : Fin A.n} (hVk : V ⊆ (A.chart k).source) {W : Fin d → Set Y} {j : Fin d → Fin B.n}
    (hW : ∀ i, IsOpen (W i)) (hdis : Pairwise (Function.onFun Disjoint W))
    (hpre : h ⁻¹' V = ⋃ i, W i) (hsh : ∀ i, Set.BijOn h (W i) V ∧ W i ⊆ (B.chart (j i)).source)
    (g : X → ℝ) (hg : MIntegrable A Φ g) :
    (∀ j', IntegrableOn (fun y => Q.χ j' ((B.chart j').symm y) *
        (E.indicator g (h ((B.chart j').symm y))) *
        locDens B (fun i => (Φ i).pullback h hh.1) j' y) (B.chart j').target) ∧
    integralWith B Q (fun i => (Φ i).pullback h hh.1) (fun y => E.indicator g (h y)) =
      d * integralWith A P Φ (E.indicator g) := by sorry
