-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_inclA__76fc8e51f144
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_inclA__76fc8e51f144
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:36.122029+00:00
-- url     : https://prove2.me/theorems/94fa2310-2b4d-4f89-a5ca-890d13b686db
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A incl A  76fc8e51f144: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A incl A  76fc8e51f144
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A incl A  76fc8e51f144 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A incl A  76fc8e51f144 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L112-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
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
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_inclA__76fc8e51f144 (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«sigA_inclA'» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_inclA__76fc8e51f144
