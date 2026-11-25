-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_tendstoUniformlyOn_of_norm_le_1e802fc55f8c
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_tendstoUniformlyOn_of_norm_le_1e802fc55f8c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:05.931005+00:00
-- url     : https://prove2.me/theorems/3367e373-163e-5142-bf2e-ceed3830f8b7
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas tendsto Uniformly On of norm le 1e802fc55f8c: P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lem
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas tendsto Uniformly On of norm le 1e802fc55f8c construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas tendsto Uniformly On of norm le 1e802fc55f8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L91-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_tendstoUniformlyOn_of_norm_le_1e802fc55f8c {Y α : Type*} [SeminormedAddCommGroup α] {F : ℝ → Y → α}
    {f : Y → α} {K : Set Y} {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ K, ‖F t y - f y‖ ≤ β t) :
    TendstoUniformlyOn F f (𝓝[>] 0) K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«ArgumentConvergenceLemmas».«tendstoUniformlyOn_of_norm_le» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_tendstoUniformlyOn_of_norm_le_1e802fc55f8c
