-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_quad_diag
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.quad_diag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:02:36.981983+00:00
-- url     : https://prove2.me/theorems/d5db2ca3-84f0-5e7b-acfb-aeb39d2355c1
-- title:
--   Semi Pt: quad diag
-- statement:
--   The Semi Pt construction uses the quad diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegM.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegM.lean#L50-L55

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.quad_diag {r : ℕ} (d w : Fin r → ℂ) :
    star w ⬝ᵥ (diagonal d *ᵥ w) = ∑ a, d a * ((‖w a‖ ^ 2 : ℝ) : ℂ) := by sorry
