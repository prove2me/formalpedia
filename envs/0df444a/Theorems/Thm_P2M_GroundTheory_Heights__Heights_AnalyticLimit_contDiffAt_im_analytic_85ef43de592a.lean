-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_im_analytic_85ef43de592a
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_im_analytic_85ef43de592a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:13.295481+00:00
-- url     : https://prove2.me/theorems/c53902bd-819a-4fa4-b6c0-8c4cf1b4d682
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit cont Diff At im analytic 85ef43de592a: P2 M Ground Theory Heights  Heights Analytic Limit cont Diff At im analytic 85ef43de592a
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit cont Diff At im analytic 85ef43de592a construction uses the P2 M Ground Theory Heights  Heights Analytic Limit cont Diff At im analytic 85ef43de592a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L76-L78

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_im_analytic_85ef43de592a {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) :
    ContDiffAt ℝ 2 (fun z => (S z).im) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«contDiffAt_im_analytic» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_contDiffAt_im_analytic_85ef43de592a
