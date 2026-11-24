-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
-- name    : ReciprocityTheory.AnForm.continuousOn_levi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:23.649613+00:00
-- url     : https://prove2.me/theorems/90388efc-7bec-43d6-8d08-f37fb0434208
-- title:
--   An Form: continuous On levi
-- statement:
--   The An Form construction uses the continuous On levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L126-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L126-L137

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

theorem ReciprocityTheory.AnForm.continuousOn_levi {φ : (ι → ℂ) → ℝ} {U : Set (ι → ℂ)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) :
    ContinuousOn (fun p : (ι → ℂ) × (ι → ℂ) => levi φ p.1 p.2) (U ×ˢ Set.univ) := by sorry
