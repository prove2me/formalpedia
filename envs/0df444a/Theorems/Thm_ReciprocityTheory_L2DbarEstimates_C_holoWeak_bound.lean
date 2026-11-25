-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holoWeak_bound
-- name    : ReciprocityTheory.L2DbarEstimates.C.holoWeak_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:34.581741+00:00
-- url     : https://prove2.me/theorems/d804da28-0fa9-4704-aa68-edfe7c5ee913
-- title:
--   C: holo Weak bound
-- statement:
--   The C construction uses the holo Weak bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/HoloWeak.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/HoloWeak.lean#L9-L12

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_Lemmata_MiscLemmasF_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
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

theorem ReciprocityTheory.L2DbarEstimates.C.holoWeak_bound {n : ℕ} {Ω K : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hu : DifferentiableOn ℂ u Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (v : V n) :
    ∃ C : ℝ, ∀ x ∈ K, ‖fderiv ℝ u x v‖ ≤ C := by sorry
