-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_integral_fsDens_inv
-- name    : ReciprocityTheory.AnForm.integral_fsDens_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:24.354135+00:00
-- url     : https://prove2.me/theorems/117f2838-a3a5-50cf-a8bf-676829fad27e
-- title:
--   An Form: integral fs Dens inv
-- statement:
--   The An Form construction uses the integral fs Dens inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L171-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L171-L202

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

theorem ReciprocityTheory.AnForm.integral_fsDens_inv (g : ℂ → ℝ) :
    ∫ z, g z⁻¹ * fsDens z = ∫ z, g z * fsDens z := by sorry
