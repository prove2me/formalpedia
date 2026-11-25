-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_gradMat_comp_e702841e1d36
-- name    : P2M_GroundTheory_Heights__Heights_MaDensChain_gradMat_comp_e702841e1d36
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:43.261936+00:00
-- url     : https://prove2.me/theorems/a09488bf-8220-48aa-9336-5a411041dafb
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Chain grad Mat comp e702841e1d36: P2 M Ground Theory Heights  Heights Ma Dens Chain grad Mat comp e702841e1d36
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Chain grad Mat comp e702841e1d36 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Chain grad Mat comp e702841e1d36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensChain.lean#L63-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensChain
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensChain_gradMat_comp_e702841e1d36 (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℝ F (g z)) (hg : DifferentiableAt ℝ g z) :
    gradMat (F ∘ g) (F ∘ g) z = ((deriv F (g z) ^ 2 : ℝ) : ℂ) • gradMat g g z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensChain».«gradMat_comp» := P2M_GroundTheory_Heights__Heights_MaDensChain_gradMat_comp_e702841e1d36
