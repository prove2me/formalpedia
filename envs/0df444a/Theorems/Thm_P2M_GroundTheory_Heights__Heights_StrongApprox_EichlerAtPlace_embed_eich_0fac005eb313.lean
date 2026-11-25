-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_embed_eich_0fac005eb313
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_embed_eich_0fac005eb313
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:11.964485+00:00
-- url     : https://prove2.me/theorems/4a9ed713-0b7b-4079-8410-a492886da74a
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place embed eich 0fac005eb313: P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place embed eich 0fac005eb313
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place embed eich 0fac005eb313 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place embed eich 0fac005eb313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L46-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PEichlerAtPlace.lean#L46-L73

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_embed_eich_0fac005eb313 (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (e : Fin N → E) (u : Fin N → Kv E v) (c' : Kv E v) :
    embed E v (eich (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) u c') =
      eich (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (singleV E v ∘ u) (singleV E v c') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerAtPlace».«embed_eich» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_embed_eich_0fac005eb313
