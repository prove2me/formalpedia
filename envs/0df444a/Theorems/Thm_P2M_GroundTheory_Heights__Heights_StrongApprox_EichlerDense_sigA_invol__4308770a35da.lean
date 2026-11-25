-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_invol__4308770a35da
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_invol__4308770a35da
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:40.883748+00:00
-- url     : https://prove2.me/theorems/41531e23-593d-4637-b143-49c1b22840b7
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A invol  4308770a35da: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A invol  4308770a35da
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A invol  4308770a35da construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense sig A invol  4308770a35da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L116-L121

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_invol__4308770a35da (c : E ≃ₐ[F] E) (hc2 : ∀ x, c (c x) = x) (a : AE F E) :
    sigA c (sigA c a) = a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«sigA_invol'» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_invol__4308770a35da
