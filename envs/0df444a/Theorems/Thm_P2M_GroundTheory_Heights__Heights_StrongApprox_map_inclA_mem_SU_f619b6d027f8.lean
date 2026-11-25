-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_map_inclA_mem_SU_f619b6d027f8
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_map_inclA_mem_SU_f619b6d027f8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:45.774786+00:00
-- url     : https://prove2.me/theorems/6e59103b-7c00-5a19-86e5-1f77cf5c6a8e
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx map incl A mem SU f619b6d027f8: P2 M Ground Theory Heights  Heights Strong Approx map incl A mem SU f619b6d027f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx map incl A mem SU f619b6d027f8 construction uses the P2 M Ground Theory Heights  Heights Strong Approx map incl A mem SU f619b6d027f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAOpenHolds.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAOpenHolds.lean#L11-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PSAOpenHolds
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_map_inclA_mem_SU_f619b6d027f8 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«map_inclA_mem_SU» := P2M_GroundTheory_Heights__Heights_StrongApprox_map_inclA_mem_SU_f619b6d027f8
