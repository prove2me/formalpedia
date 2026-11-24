-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__spaces_signature_eq_b068484ac5cc
-- name    : P2M_Formalism_BasicNotions_Examples__spaces_signature_eq_b068484ac5cc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:20:56.51713+00:00
-- url     : https://prove2.me/theorems/5bdf3a67-fb29-4acc-a2d0-86778afee1d2
-- title:
--   P2 M Formalism Basic Notions Examples  spaces signature eq b068484ac5cc: P2 M Formalism Basic Notions Examples  spaces signature eq b068484ac5cc
-- statement:
--   The P2 M Formalism Basic Notions Examples  spaces signature eq b068484ac5cc construction uses the P2 M Formalism Basic Notions Examples  spaces signature eq b068484ac5cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BaseFormAnisotropicOrthogonalSingle.lean#L390-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BaseFormAnisotropicOrthogonalSingle.lean#L390-L391

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BaseFormAnisotropicOrthogonalSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

theorem P2M_Formalism_BasicNotions_Examples__spaces_signature_eq_b068484ac5cc : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ,
    ((spacesOfRanks R hstar cm T hT pz hpz hy).Y j).sig τ = sigYD R j := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«spaces_signature_eq» := P2M_Formalism_BasicNotions_Examples__spaces_signature_eq_b068484ac5cc
