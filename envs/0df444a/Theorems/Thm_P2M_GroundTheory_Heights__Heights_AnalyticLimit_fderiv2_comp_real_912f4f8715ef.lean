-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_comp_real_912f4f8715ef
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_comp_real_912f4f8715ef
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:24.312911+00:00
-- url     : https://prove2.me/theorems/73086910-85af-4e1f-a5d5-13e8c2ebce45
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 comp real 912f4f8715ef: P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 comp real 912f4f8715ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 comp real 912f4f8715ef construction uses the P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 comp real 912f4f8715ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L14-L29

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_comp_real_912f4f8715ef {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (v w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => G (ψ z))) y v w =
      G₁ (ψ y) * fderiv ℝ (fderiv ℝ ψ) y v w + g₂ * fderiv ℝ ψ y v * fderiv ℝ ψ y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«fderiv2_comp_real» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_comp_real_912f4f8715ef
