-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_normSq_analytic_a0251b8db114
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_normSq_analytic_a0251b8db114
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:13.666451+00:00
-- url     : https://prove2.me/theorems/e088ab7b-48a0-4707-b65d-733479dab39e
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit fderiv norm Sq analytic a0251b8db114: P2 M Ground Theory Heights  Heights Analytic Limit fderiv norm Sq analytic a0251b8db114
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit fderiv norm Sq analytic a0251b8db114 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit fderiv norm Sq analytic a0251b8db114 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L107-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L107-L123

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_normSq_analytic_a0251b8db114 {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => ‖S z‖ ^ 2) y v =
      2 * ((S y).re * (fderiv ℂ S y v).re + (S y).im * (fderiv ℂ S y v).im) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«fderiv_normSq_analytic» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_normSq_analytic_a0251b8db114
