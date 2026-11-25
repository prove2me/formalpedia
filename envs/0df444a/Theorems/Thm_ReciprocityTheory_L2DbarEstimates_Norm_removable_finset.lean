-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_removable_finset
-- name    : ReciprocityTheory.L2DbarEstimates.Norm.removable_finset
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:07.103878+00:00
-- url     : https://prove2.me/theorems/5123917c-fbf3-5c68-ba77-335cbb72fde6
-- title:
--   Norm: removable finset
-- statement:
--   The Norm construction uses the removable finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/RemovableFinset.lean#L9-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SymmetricSections/RemovableFinset.lean#L9-L63

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_RemovableFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u

theorem ReciprocityTheory.L2DbarEstimates.Norm.removable_finset (S : Finset ℂ) : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (↑S)ᶜ →
    (∀ c ∈ S, ∃ M : ℝ, ∀ᶠ t in 𝓝[≠] c, ‖f t‖ ≤ M) →
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ t ∉ S, F t = f t := by sorry
