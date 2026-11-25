-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_zd_fderiv_symm
-- name    : ReciprocityTheory.L2DbarEstimates.Y.zd_fderiv_symm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:57.706354+00:00
-- url     : https://prove2.me/theorems/562b7e6e-5c7c-4acf-84d8-e2e6d76c1e2d
-- title:
--   Y: zd fderiv symm
-- statement:
--   The Y construction uses the zd fderiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZeroDimA.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZeroDimA.lean#L14-L22

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

theorem ReciprocityTheory.L2DbarEstimates.Y.zd_fderiv_symm {k : ℕ} {g : E → ContinuousMultilinearMap ℂ (fun _ : Fin k => E) F}
    {y : E} (h : ∀ᶠ z in 𝓝 y, ∀ (τ : Equiv.Perm (Fin k)) (w : Fin k → E), g z (w ∘ τ) = g z w)
    (τ : Equiv.Perm (Fin k)) (u : E) (w : Fin k → E) :
    fderiv ℂ g y u (w ∘ τ) = fderiv ℂ g y u w := by sorry
