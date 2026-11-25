-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_maDens_congr_germ__6458652e2d6a
-- name    : P2M_GroundTheory_Heights__Heights_FourB_maDens_congr_germ__6458652e2d6a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:52.87706+00:00
-- url     : https://prove2.me/theorems/ef552fcb-9c43-5431-933d-d935f6bc42b0
-- title:
--   P2 M Ground Theory Heights  Heights Four B ma Dens congr germ  6458652e2d6a: P2 M Ground Theory Heights  Heights Four B ma Dens congr germ  6458652e2d6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B ma Dens congr germ  6458652e2d6a construction uses the P2 M Ground Theory Heights  Heights Four B ma Dens congr germ  6458652e2d6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OfFubiniStudyCoverMass.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OfFubiniStudyCoverMass.lean#L94-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open OpenSetChart

theorem P2M_GroundTheory_Heights__Heights_FourB_maDens_congr_germ__6458652e2d6a {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«maDens_congr_germ'» := P2M_GroundTheory_Heights__Heights_FourB_maDens_congr_germ__6458652e2d6a
