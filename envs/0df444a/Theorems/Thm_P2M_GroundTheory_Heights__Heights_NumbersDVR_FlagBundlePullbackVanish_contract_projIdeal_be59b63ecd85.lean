-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_contract_projIdeal_be59b63ecd85
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_contract_projIdeal_be59b63ecd85
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:48.413164+00:00
-- url     : https://prove2.me/theorems/b0f27404-66cb-469d-8fa9-118f9a5e0922
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish contract proj Ideal be59b63ecd85: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish contract proj
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish contract proj Ideal be59b63ecd85 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Pullback Vanish contract proj Ideal be59b63ecd85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundlePullbackVanish.lean#L23-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundlePullbackVanish.lean#L23-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundlePullbackVanish
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_contract_projIdeal_be59b63ecd85 {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
    {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) {N M : ℕ} {E : Type} [AddCommGroup E]
    [Module Ω E] (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ) :
    FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M (Function.Embedding.some k)) F y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundlePullbackVanish».«contract_projIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_contract_projIdeal_be59b63ecd85
