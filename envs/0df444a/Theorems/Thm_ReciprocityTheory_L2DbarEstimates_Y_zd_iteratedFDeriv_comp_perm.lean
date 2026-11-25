-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_zd_iteratedFDeriv_comp_perm
-- name    : ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:28.216814+00:00
-- url     : https://prove2.me/theorems/c70350a2-418f-4c1c-a112-5390fb742fe3
-- title:
--   Y: zd iterated FDeriv comp perm
-- statement:
--   The Y construction uses the zd iterated FDeriv comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZeroDimA.lean#L31-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZeroDimA.lean#L31-L129

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

theorem ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) :
    ∀ k, ∀ y ∈ U, ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E),
      iteratedFDeriv ℂ k f y (v ∘ σ) = iteratedFDeriv ℂ k f y v := by sorry
