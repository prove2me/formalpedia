-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_eq_zero_on_ball
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_on_ball
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:20.66015+00:00
-- url     : https://prove2.me/theorems/846f2d6f-c82b-4210-a3ed-3e911ac6132e
-- title:
--   Pf: eq zero on ball
-- statement:
--   The Pf construction uses the eq zero on ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EqZeroOfMulEqZero.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EqZeroOfMulEqZero.lean#L10-L12

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaJ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EqZeroOfMulEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
open Metric Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_on_ball {g : V → ℂ} {x : V} {ε : ℝ} (hg : DifferentiableOn ℂ g (ball x ε)) {z : V}
    (hz : z ∈ ball x ε) (hgz : g =ᶠ[𝓝 z] 0) : ∀ y ∈ ball x ε, g y = 0 := by sorry
