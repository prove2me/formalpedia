-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_exists_coords_ec5c050ef0b1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_exists_coords_ec5c050ef0b1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:01.890487+00:00
-- url     : https://prove2.me/theorems/a32f8026-7802-50b5-8fbd-51d53ee6d17d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg exists coords ec5c050ef0b1: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg exists coords ec5c050ef0b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg exists coords ec5c050ef0b1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg exists coords ec5c050ef0b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L32-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L32-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagConeAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_exists_coords_ec5c050ef0b1 {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w : Module.Basis (Fin N) Ω E) (u : Fin k → E)
    (hu : ∀ q (j : Fin N), k ≤ (j : ℕ) → w.repr (u q) j = 0)
    (hdet : (Matrix.of fun q j : Fin k => w.repr (u q) (Fin.castLE hkN j)).det ≠ 0)
    (s : Fin N → Φ) (hs : ∀ j : Fin N, k ≤ (j : ℕ) → s j = 0) :
    ∃ s' : Fin k → Φ, ∀ ψ : Module.Dual Ω E,
      ∑ j, s j * algebraMap Ω Φ (ψ (w j)) = ∑ q, s' q * algebraMap Ω Φ (ψ (u q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagConeAlg».«exists_coords» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_exists_coords_ec5c050ef0b1
