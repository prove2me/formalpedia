-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_leviForm_radial
-- name    : ReciprocityTheory.AnForm.M.projLine_leviForm_radial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:49.132738+00:00
-- url     : https://prove2.me/theorems/c9693a07-511c-4fbd-bacb-43485494f0d6
-- title:
--   M: proj Line levi Form radial
-- statement:
--   The M construction uses the proj Line levi Form radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L48-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L48-L72

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.M.projLine_leviForm_radial {F : (Fin 1 → ℂ) → ℝ} {G G' : ℝ → ℝ} {G'' : ℝ} {y : Fin 1 → ℂ}
    (hF : ∀ᶠ w in 𝓝 y, F w = G (‖w 0‖ ^ 2))
    (hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt G (G' t) t)
    (hG' : HasDerivAt G' G'' (‖y 0‖ ^ 2)) (v : Fin 1 → ℂ) :
    levi F y v = (G'' * ‖y 0‖ ^ 2 + G' (‖y 0‖ ^ 2)) * ‖v 0‖ ^ 2 := by sorry
