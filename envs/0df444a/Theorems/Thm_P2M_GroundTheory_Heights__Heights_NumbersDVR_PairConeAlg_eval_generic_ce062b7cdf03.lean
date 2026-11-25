-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_eval_generic_ce062b7cdf03
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_eval_generic_ce062b7cdf03
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:44.943309+00:00
-- url     : https://prove2.me/theorems/67ca06f8-2eb3-4ecd-9750-32573141eba8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg eval generic ce062b7cdf03: P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg eval generic ce062b7cdf03
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg eval generic ce062b7cdf03 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Alg eval generic ce062b7cdf03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeAlg.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeAlg.lean#L14-L26

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_eval_generic_ce062b7cdf03 {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N : ℕ} (e u : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (ψ : Module.Dual Ω E) :
    ∑ i, t i * algebraMap Ω Φ (ψ (e i)) =
      ∑ q, (∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * algebraMap Ω Φ (ψ (u q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairConeAlg».«eval_generic» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_eval_generic_ce062b7cdf03
