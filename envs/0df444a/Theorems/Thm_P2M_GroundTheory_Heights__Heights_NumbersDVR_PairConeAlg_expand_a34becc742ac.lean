-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_expand_a34becc742ac
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_expand_a34becc742ac
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:34.541896+00:00
-- url     : https://prove2.me/theorems/c426e24d-31c4-48c4-b95b-59f40c06bd16
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg expand a34becc742ac: P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg expand a34becc742ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg expand a34becc742ac construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg expand a34becc742ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeAlg.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeAlg.lean#L28-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_expand_a34becc742ac {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N : ℕ} {σ : Type*} (e u : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (ψ : Module.Dual Ω E) (Y Z : Ω) (o : σ) :
    ∑ q, C (algebraMap Ω Φ (ψ (u q) / Z)) *
        (C (algebraMap Ω Φ Y * ∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * (X o : MvPolynomial σ Φ)) =
      C (algebraMap Ω Φ (Y / Z) * ∑ i, t i * algebraMap Ω Φ (ψ (e i))) * X o := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairConeAlg».«expand» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_expand_a34becc742ac
