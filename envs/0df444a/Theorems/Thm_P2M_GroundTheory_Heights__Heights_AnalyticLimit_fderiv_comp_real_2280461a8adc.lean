-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_comp_real_2280461a8adc
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_comp_real_2280461a8adc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:30.589989+00:00
-- url     : https://prove2.me/theorems/93cc6508-e2f7-453c-bf63-a0ea7e92711a
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit fderiv comp real 2280461a8adc: P2 M Ground Theory Heights  Heights Analytic Limit fderiv comp real 2280461a8adc
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit fderiv comp real 2280461a8adc construction uses the P2 M Ground Theory Heights  Heights Analytic Limit fderiv comp real 2280461a8adc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L31-L36

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_comp_real_2280461a8adc {ψ : (ι → ℂ) → ℝ} {G : ℝ → ℝ} {g₁ : ℝ} {y : ι → ℂ}
    (hψ : DifferentiableAt ℝ ψ y) (hG : HasDerivAt G g₁ (ψ y)) (v : ι → ℂ) :
    fderiv ℝ (fun z => G (ψ z)) y v = g₁ * fderiv ℝ ψ y v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«fderiv_comp_real» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv_comp_real_2280461a8adc
