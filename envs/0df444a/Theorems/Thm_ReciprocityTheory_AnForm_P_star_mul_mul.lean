-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_star_mul_mul
-- name    : ReciprocityTheory.AnForm.P.star_mul_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:52.126105+00:00
-- url     : https://prove2.me/theorems/26fc8db4-dbc4-47a0-a1b3-e7261a53d0a7
-- title:
--   P: star mul mul
-- statement:
--   The P construction uses the star mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean#L124-L127

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial

theorem ReciprocityTheory.AnForm.P.star_mul_mul (h : ℝ) (z : ℂ) : star z * ((h : ℂ) * z) = ((h * ‖z‖ ^ 2 : ℝ) : ℂ) := by sorry
