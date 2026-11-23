-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
-- name    : ReciprocityTheory.AnForm.levi_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:26.934797+00:00
-- url     : https://prove2.me/theorems/7ecded61-abe9-4354-b71c-2f060dc2d5f5
-- title:
--   An Form: levi comp
-- statement:
--   The An Form construction uses the levi comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L38-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L38-L67

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem ReciprocityTheory.AnForm.levi_comp {φ : (κ → ℂ) → ℝ} {τ : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (w : ι → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    levi (φ ∘ τ) z w = levi φ (τ z) (fderiv ℂ τ z w) := by sorry
