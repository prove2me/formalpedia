-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_fderiv_fderiv_radial
-- name    : ReciprocityTheory.AnForm.fderiv_fderiv_radial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:16.273706+00:00
-- url     : https://prove2.me/theorems/1daeda05-0e47-52bb-8088-a1bea179cde3
-- title:
--   An Form: fderiv fderiv radial
-- statement:
--   The An Form construction uses the fderiv fderiv radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L21-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L21-L54

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section

theorem ReciprocityTheory.AnForm.fderiv_fderiv_radial (h h' h'' : ℝ → ℝ) (z : Fin 1 → ℂ)
    (hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt h (h' t) t)
    (hd2 : HasDerivAt h' (h'' (‖z 0‖ ^ 2)) (‖z 0‖ ^ 2)) (w : Fin 1 → ℂ) :
    fderiv ℝ (fderiv ℝ fun y : Fin 1 → ℂ => h (‖y 0‖ ^ 2)) z w w =
      h'' (‖z 0‖ ^ 2) * (2 * inner ℝ (z 0) (w 0)) ^ 2 + h' (‖z 0‖ ^ 2) * (2 * ‖w 0‖ ^ 2) := by sorry
