-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_eq_zero_of_mul_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:41.278642+00:00
-- url     : https://prove2.me/theorems/a21fa3ce-8b03-486a-84ef-5d998fd0c317
-- title:
--   Pf: eq zero of mul eq zero
-- statement:
--   The Pf construction uses the eq zero of mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EqZeroOfMulEqZero.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EqZeroOfMulEqZero.lean#L28-L34

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {f g : V → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hfg : ∀ y ∈ U, f y * g y = 0)
    {x0 : V} (hx0 : x0 ∈ U) (h0 : f x0 ≠ 0) : ∀ y ∈ U, g y = 0 := by sorry
