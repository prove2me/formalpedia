-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:36.997123+00:00
-- url     : https://prove2.me/theorems/6f118fe3-2a7e-4608-ada9-f84e0a1d71a0
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit fderiv re analytic f165eb17d640: P2 M Ground Theory Heights  Heights Analytic Limit fderiv re analytic f165eb17d640
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit fderiv re analytic f165eb17d640 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit fderiv re analytic f165eb17d640 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L47-L53

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640 {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).re) y v = (fderiv ℂ S y v).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«fderiv_re_analytic» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_re_analytic_f165eb17d640
