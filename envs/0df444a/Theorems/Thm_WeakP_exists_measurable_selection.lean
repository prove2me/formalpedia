-- Prove2me | Theorems.Thm_WeakP_exists_measurable_selection
-- name    : WeakP.exists_measurable_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:33.06573+00:00
-- url     : https://prove2.me/theorems/7dbcfb5f-9b11-4f20-997e-b82f23c775c2
-- title:
--   Weak P: exists measurable selection
-- statement:
--   Kuratowski–Ryll-Nardzewski selection with `WeakP` targets: the Polish
--       wrapper of `exists_measurable_selection` (the metric upgrade keeps the
--       topology, hence the Borel structure — the §3W C3 pattern).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L49-L57
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L49-L57

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_exists_measurable_selection

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section

theorem WeakP.exists_measurable_selection {α : Type*} [MeasurableSpace α]
    {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [PolishSpace W]
    [BorelSpace W]
    {Φ : α → Set (WeakP W)} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set (WeakP W), IsOpen U →
      MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → WeakP W, Measurable f ∧ ∀ a, f a ∈ Φ a := by sorry
