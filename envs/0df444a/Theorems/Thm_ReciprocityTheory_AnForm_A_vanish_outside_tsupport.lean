-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_vanish_outside_tsupport
-- name    : ReciprocityTheory.AnForm.A.vanish_outside_tsupport
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:18.297404+00:00
-- url     : https://prove2.me/theorems/dc3b128e-219a-51a4-939d-a86be720df2d
-- title:
--   A: vanish outside tsupport
-- statement:
--   The A construction uses the vanish outside tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L153-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L153-L176

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
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

theorem ReciprocityTheory.AnForm.A.vanish_outside_tsupport {D : ℕ} {v : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (hy : y ∉ tsupport v) :
    cplx v =ᶠ[𝓝 y] (fun _ => 0) ∧ (∀ k, dzb k (cplx v) =ᶠ[𝓝 y] fun _ => 0) ∧
      fderiv ℝ (fderiv ℝ v) y = 0 := by sorry
