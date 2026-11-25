-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_contDiffOn_complex
-- name    : ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:30.22634+00:00
-- url     : https://prove2.me/theorems/cc1f2ee8-d1cb-4eb5-a229-8cf1eba41e29
-- title:
--   C: holo cont Diff On complex
-- statement:
--   The C construction uses the holo cont Diff On complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/HoloContDiffAtComplex.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/HoloContDiffAtComplex.lean#L23-L25

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExistsClmOfI
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffAtComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open Metric Set Filter Topology Complex
open scoped ContDiff

theorem ReciprocityTheory.L2DbarEstimates.C.holo_contDiffOn_complex {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℂ ∞ f Ω := by sorry
