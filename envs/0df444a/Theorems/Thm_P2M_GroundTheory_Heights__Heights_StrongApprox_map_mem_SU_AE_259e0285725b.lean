-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_map_mem_SU_AE_259e0285725b
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_map_mem_SU_AE_259e0285725b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:19.95391+00:00
-- url     : https://prove2.me/theorems/79ce4a47-b8a7-488b-b101-05e51a4cfa9c
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx map mem SU AE 259e0285725b: P2 M Ground Theory Heights  Heights Strong Approx map mem SU AE 259e0285725b
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx map mem SU AE 259e0285725b construction uses the P2 M Ground Theory Heights  Heights Strong Approx map mem SU AE 259e0285725b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PClosureIsSubmonoid.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PClosureIsSubmonoid.lean#L28-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PClosureIsSubmonoid
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_map_mem_SU_AE_259e0285725b {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«map_mem_SU_AE» := P2M_GroundTheory_Heights__Heights_StrongApprox_map_mem_SU_AE_259e0285725b
