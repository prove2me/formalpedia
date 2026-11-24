-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_comp_real_4d15d05546d6
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_comp_real_4d15d05546d6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:53.235893+00:00
-- url     : https://prove2.me/theorems/840128ea-a67c-4545-8f75-dedf9714ad88
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit levi comp real 4d15d05546d6: P2 M Ground Theory Heights  Heights Analytic Limit levi comp real 4d15d05546d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit levi comp real 4d15d05546d6 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit levi comp real 4d15d05546d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L38-L45

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_comp_real_4d15d05546d6 {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (w : ι → ℂ) :
    levi (fun z => G (ψ z)) y w = G₁ (ψ y) * levi ψ y w +
      g₂ * ((fderiv ℝ ψ y w) ^ 2 + (fderiv ℝ ψ y (Complex.I • w)) ^ 2) / 4 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«levi_comp_real» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_comp_real_4d15d05546d6
