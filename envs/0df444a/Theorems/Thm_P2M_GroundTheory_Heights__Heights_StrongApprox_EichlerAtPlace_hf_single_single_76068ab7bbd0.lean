-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_single_76068ab7bbd0
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_single_76068ab7bbd0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:55.404294+00:00
-- url     : https://prove2.me/theorems/b86b09d6-17b9-5c06-a104-09b30ce25327
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single single 76068ab7bbd0: P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single single 76068ab7bbd0
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single single 76068ab7bbd0 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single single 76068ab7bbd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L34-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
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
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_single_76068ab7bbd0 (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    (hmul : ∀ x y : Kv E v, singleV E v (x * y) = singleV E v x * singleV E v y)
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u w : Fin N → Kv E v) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (singleV E v ∘ w) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerAtPlace».«hf_single_single» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_single_76068ab7bbd0
