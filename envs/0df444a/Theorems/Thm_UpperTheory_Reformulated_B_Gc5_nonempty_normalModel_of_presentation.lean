-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Gc5_nonempty_normalModel_of_presentation
-- name    : UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:46.492185+00:00
-- url     : https://prove2.me/theorems/610c4547-8d99-4593-93c2-c6415c3d9650
-- title:
--   Gc5: nonempty normal Model of presentation
-- statement:
--   The Gc5 construction uses the nonempty normal Model of presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NonemptyNormalModelOfPresentation.lean#L56-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NonemptyNormalModelOfPresentation.lean#L56-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteOfFiniteOverNormal
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NonemptyNormalModelOfPresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation :
    ∀ {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type) [inst : CommRing R] [IsDomain R] [inst_2 : Algebra ℂ R]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R),
    Function.Surjective (⇑π : MvPolynomial (Fin n) ℂ → R) →
      RingHom.ker π = J →
        Nonempty
          (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel
            J) := by sorry
