-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yt7_lift_finite
-- name    : UpperTheory.Reformulated.B.Yt7.lift_finite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:09:16.840705+00:00
-- url     : https://prove2.me/theorems/97c555b4-33c0-477c-89bc-6dad3c50ef80
-- title:
--   Yt7: lift finite
-- statement:
--   The Yt7 construction uses the lift finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SectionLift.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SectionLift.lean#L62-L77

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SectionLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yt7.lift_finite :
    ∀ {R K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K]
      [IsIntegrallyClosed R] {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f]
      (y : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ S) (w : UpperTheory.Reformulated.B.Yt7.Sp K ⟶ X),
      CategoryTheory.CategoryStruct.comp w f =
          CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) y →
        ∃ (v : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ X),
          CategoryTheory.CategoryStruct.comp v f = y ∧
            CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) v = w := by sorry
