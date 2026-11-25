-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_incl_598849498d15
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_incl_598849498d15
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:09.673607+00:00
-- url     : https://prove2.me/theorems/42d18743-391c-4ac7-8267-9b1ce1118414
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single incl 598849498d15: P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single incl 598849498d15
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single incl 598849498d15 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hf single incl 598849498d15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L24-L32

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_incl_598849498d15 (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u : Fin N → Kv E v) (y : Fin N → E) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (inclA F E ∘ y) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u (inclV E v ∘ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerAtPlace».«hf_single_incl» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_incl_598849498d15
