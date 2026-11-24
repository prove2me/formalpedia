-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_im_analytic_7493638fe9a1
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_im_analytic_7493638fe9a1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:39.971931+00:00
-- url     : https://prove2.me/theorems/27160a3a-224f-4575-9948-5d5bc0384713
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit fderiv im analytic 7493638fe9a1: P2 M Ground Theory Heights  Heights Analytic Limit fderiv im analytic 7493638fe9a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit fderiv im analytic 7493638fe9a1 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit fderiv im analytic 7493638fe9a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L58-L63

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_im_analytic_7493638fe9a1 {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).im) y v = (fderiv ℂ S y v).im := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«fderiv_im_analytic» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_im_analytic_7493638fe9a1
