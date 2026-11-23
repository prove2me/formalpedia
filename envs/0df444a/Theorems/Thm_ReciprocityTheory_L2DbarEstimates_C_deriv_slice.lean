-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_deriv_slice
-- name    : ReciprocityTheory.L2DbarEstimates.C.deriv_slice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:35.844194+00:00
-- url     : https://prove2.me/theorems/01a31de8-a29c-4fdc-8529-dec1ef3a312e
-- title:
--   C: deriv slice
-- statement:
--   The C construction uses the deriv slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L108-L114

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.deriv_slice {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} {l : ℂ} (hw : z + l • e ∈ Ω) :
    deriv (fun m : ℂ => F (z + m • e)) l = fderiv ℂ F (z + l • e) e := by sorry
