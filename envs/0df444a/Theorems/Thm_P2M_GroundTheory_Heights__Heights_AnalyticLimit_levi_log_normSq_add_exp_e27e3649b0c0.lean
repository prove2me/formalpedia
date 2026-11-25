-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_log_normSq_add_exp_e27e3649b0c0
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_log_normSq_add_exp_e27e3649b0c0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:34.403117+00:00
-- url     : https://prove2.me/theorems/2a8473f5-7c68-4e76-b54a-6116e64df08d
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit levi log norm Sq add exp e27e3649b0c0: P2 M Ground Theory Heights  Heights Analytic Limit levi log norm Sq add exp e27e3649b0c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit levi log norm Sq add exp e27e3649b0c0 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit levi log norm Sq add exp e27e3649b0c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L125-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L125-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_log_normSq_add_exp_e27e3649b0c0 {S : (ι → ℂ) → ℂ} {Φ : (ι → ℂ) → ℝ} {y : ι → ℂ} {ε : ℝ}
    (hS : AnalyticAt ℂ S y) (hΦ : ContDiffAt ℝ 2 Φ y) (hε : 0 < ε) (w : ι → ℂ) :
    2 * (ε * Real.exp (2 * Φ y)) / (‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)) * levi Φ y w ≤
      levi (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«levi_log_normSq_add_exp» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_log_normSq_add_exp_e27e3649b0c0
