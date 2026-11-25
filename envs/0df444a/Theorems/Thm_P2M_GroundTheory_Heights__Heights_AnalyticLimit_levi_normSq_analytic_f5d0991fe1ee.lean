-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_normSq_analytic_f5d0991fe1ee
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_normSq_analytic_f5d0991fe1ee
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:07.14023+00:00
-- url     : https://prove2.me/theorems/735ac744-c9d8-449e-ada7-d4cbbc98782a
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit levi norm Sq analytic f5d0991fe1ee: P2 M Ground Theory Heights  Heights Analytic Limit levi norm Sq analytic f5d0991fe1ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit levi norm Sq analytic f5d0991fe1ee construction uses the P2 M Ground Theory Heights  Heights Analytic Limit levi norm Sq analytic f5d0991fe1ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L87-L105

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_normSq_analytic_f5d0991fe1ee {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => ‖S z‖ ^ 2) y w = ‖fderiv ℂ S y w‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«levi_normSq_analytic» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_normSq_analytic_f5d0991fe1ee
