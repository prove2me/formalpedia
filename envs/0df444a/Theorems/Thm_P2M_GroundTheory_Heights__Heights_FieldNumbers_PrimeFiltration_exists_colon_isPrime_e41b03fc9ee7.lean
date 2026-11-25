-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_colon_isPrime_e41b03fc9ee7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_colon_isPrime_e41b03fc9ee7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:49.820892+00:00
-- url     : https://prove2.me/theorems/52a1b856-f53c-5f14-9420-be5146174b46
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists colon is Prime e41b03fc9ee7: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists colon is Prime e41b03fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists colon is Prime e41b03fc9ee7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists colon is Prime e41b03fc9ee7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L142-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L142-L179

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_colon_isPrime_e41b03fc9ee7 [∀ k, Fintype (ι k)] {J : Ideal (MRing ι F)}
    (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (c : K → ℕ) (s : MRing ι F), IsMultiHomog s c ∧ s ∉ J ∧
      (J.colon (Ideal.span {s})).IsPrime ∧ IsMultiHomogIdeal (J.colon (Ideal.span {s})) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«exists_colon_isPrime» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_colon_isPrime_e41b03fc9ee7
