-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_along_455a2e0f8eab
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_along_455a2e0f8eab
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:08.768977+00:00
-- url     : https://prove2.me/theorems/36a9fe8a-6aa4-4973-972d-ad68db1e44d4
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense along 455a2e0f8eab: P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense along 455a2e0f8eab
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense along 455a2e0f8eab construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler Dense along 455a2e0f8eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L123-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerDense.lean#L123-L169

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_along_455a2e0f8eab (hT : AETopologicalRing.Statement) (hD : EDenseInAE.Statement)
    (hO : OrthProjection.Statement) (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (N : ℕ) (J : Matrix (Fin N) (Fin N) E) (hJ : Jᵀ = J.map c) (e f : Fin N → E)
    (he : hf c.toRingHom J e e = 0) (hff : hf c.toRingHom J f f = 0) (hef : hf c.toRingHom J e f = 1)
    [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)] :
    eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) ⊆
      closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) ''
        eichAlong c.toRingHom J e f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerDense».«along» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_along_455a2e0f8eab
