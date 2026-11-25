-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_map_compAt_mem_SU_3b573f666034
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_map_compAt_mem_SU_3b573f666034
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:08.548294+00:00
-- url     : https://prove2.me/theorems/d0022355-08f2-517e-85f4-63cc9854d850
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx map comp At mem SU 3b573f666034: P2 M Ground Theory Heights  Heights Strong Approx map comp At mem SU 3b573f666034
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx map comp At mem SU 3b573f666034 construction uses the P2 M Ground Theory Heights  Heights Strong Approx map comp At mem SU 3b573f666034 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L82-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L82-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
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
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_map_compAt_mem_SU_3b573f666034 (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) {x : Matrix (Fin N) (Fin N) (AE F E)}
    (hx : x ∈ SU (sigA c) (J.map (inclA F E))) :
    x.map (compAt E v) ∈ SU (sigV c v).toRingHom (J.map (inclV E v)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«map_compAt_mem_SU» := P2M_GroundTheory_Heights__Heights_StrongApprox_map_compAt_mem_SU_3b573f666034
