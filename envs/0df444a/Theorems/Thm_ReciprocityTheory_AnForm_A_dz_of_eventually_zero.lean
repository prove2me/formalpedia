-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dz_of_eventually_zero
-- name    : ReciprocityTheory.AnForm.A.dz_of_eventually_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:57.581367+00:00
-- url     : https://prove2.me/theorems/18c61988-fef5-44c6-85d5-f060ad73975d
-- title:
--   A: dz of eventually zero
-- statement:
--   The A construction uses the dz of eventually zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L164-L167

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

theorem ReciprocityTheory.AnForm.A.dz_of_eventually_zero (h : f =ᶠ[𝓝 z] fun _ => 0) : dz j f z = 0 := by sorry
