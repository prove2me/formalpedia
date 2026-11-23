-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_cca_cont_theta
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.cca_cont_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:05:45.940185+00:00
-- url     : https://prove2.me/theorems/29349262-2035-4814-addc-6a0b75a0ad64
-- title:
--   S7: cca cont theta
-- statement:
--   The S7 construction uses the cca cont theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean#L13-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.S7.cca_cont_theta {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {F : X → G} {U : Set X}
    (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ) (ha : Continuous a) {z u : X}
    (hz : ∀ θ, z + a θ • u ∈ U) : Continuous (fun θ => κ θ • F (z + a θ • u)) := by sorry
