-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_apply_castLE_b8045d7b44e9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_apply_castLE_b8045d7b44e9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:30.946985+00:00
-- url     : https://prove2.me/theorems/f79a824a-e1b7-42a9-97c1-5972c10e2a0f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg apply cast LE b8045d7b44e9: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg apply cast LE b8045d7b44e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg apply cast LE b8045d7b44e9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg apply cast LE b8045d7b44e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L23-L30

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_apply_castLE_b8045d7b44e9 {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N k : ℕ} (hkN : k ≤ N)
    (w : Module.Basis (Fin N) Ω E) (v : E) (hv : ∀ j : Fin N, k ≤ (j : ℕ) → w.repr v j = 0)
    (ψ : Module.Dual Ω E) :
    ψ v = ∑ j : Fin k, w.repr v (Fin.castLE hkN j) * ψ (w (Fin.castLE hkN j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagConeAlg».«apply_castLE» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_apply_castLE_b8045d7b44e9
