-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_dz_add
-- name    : ReciprocityTheory.AnForm.A.dz_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:07.247207+00:00
-- url     : https://prove2.me/theorems/f4b80100-3445-4663-bdf2-b03619e1ad8f
-- title:
--   A: dz add
-- statement:
--   The A construction uses the dz add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L139-L149

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

theorem ReciprocityTheory.AnForm.A.dz_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (fun y => f y + g y) z = dz j f z + dz j g z := by sorry
