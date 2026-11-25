-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_AdmissibleSmoothRepresentations_isSemisimple
-- name    : UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:14.40708+00:00
-- url     : https://prove2.me/theorems/2e273d7d-a25d-4045-9f30-585426a57768
-- title:
--   Admissible Smooth Representations: is Semisimple
-- statement:
--   The Admissible Smooth Representations construction uses the is Semisimple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AdmissibleSmoothRepresentations.lean#L153-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AdmissibleSmoothRepresentations.lean#L153-L218

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AdmissibleSmoothRepresentations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple :
    ∀ {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [IsTopologicalGroup H] {V : Type}
      [inst_3 : NormedAddCommGroup V] [inst_4 : InnerProductSpace ℂ V] {ρ : Representation ℂ H V},
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsAdmissible ρ →
        (∀ (g : H) (x y : V),
            Inner.inner ℂ (((ρ : H → V →ₗ[ℂ] V) g : V → V) x) (((ρ : H → V →ₗ[ℂ] V) g : V → V) y) = Inner.inner ℂ x y) →
          ∀ {K₀ : Subgroup H}, IsOpen (↑K₀ : Set H) → IsCompact (↑K₀ : Set H) → ρ.IsSemisimpleRepresentation := by sorry
