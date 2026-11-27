-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_UnitaryAnnihilator_unitary_and_annihilator_eq
-- name    : UpperTheory.Reformulated.B.UnitaryAnnihilator.unitary_and_annihilator_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:05:16.272053+00:00
-- url     : https://prove2.me/theorems/7b45b735-1890-48c4-b345-b9bbd9c28291
-- title:
--   Unitary Annihilator: unitary and annihilator eq
-- statement:
--   The Unitary Annihilator construction uses the unitary and annihilator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitaryAnnihilator.lean#L387-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitaryAnnihilator.lean#L387-L417

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryAnnihilator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

theorem UpperTheory.Reformulated.B.UnitaryAnnihilator.unitary_and_annihilator_eq :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F]
    [LocallyCompactSpace (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)]
    [Invertible (2 : NumberField.AdeleRing (NumberField.RingOfIntegers F) F)]
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
    Continuous (⇑ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) →
      ψ ≠ (1 : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ) →
        (∀ (a : F),
            (ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ)
                ((Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                    F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                  a) =
              (1 : ℂ)) →
          (∀ (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F),
              ‖(ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) x‖ = (1 : ℝ)) ∧
            ∀ (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F),
              (∀ (a : F),
                  (ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ)
                      (x *
                        (Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                            F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                          a) =
                    (1 : ℂ)) →
                ∃ (b : F),
                  x =
                    (Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                        F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                      b := by sorry
