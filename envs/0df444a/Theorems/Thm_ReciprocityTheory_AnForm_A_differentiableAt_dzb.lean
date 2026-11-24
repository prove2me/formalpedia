-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_differentiableAt_dzb
-- name    : ReciprocityTheory.AnForm.A.differentiableAt_dzb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:53.958857+00:00
-- url     : https://prove2.me/theorems/2890f552-54a9-4714-9cd3-3dd6094f0b19
-- title:
--   A: differentiable At dzb
-- statement:
--   The A construction uses the differentiable At dzb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L174-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L174-L191

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}

theorem ReciprocityTheory.AnForm.A.differentiableAt_dzb (hf : ContDiffAt ℝ 2 f z) : DifferentiableAt ℝ (dzb j f) z := by sorry
