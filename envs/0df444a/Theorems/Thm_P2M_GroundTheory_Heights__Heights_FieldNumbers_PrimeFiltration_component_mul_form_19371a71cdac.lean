-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_mul_form_19371a71cdac
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_mul_form_19371a71cdac
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:10.952454+00:00
-- url     : https://prove2.me/theorems/8995352f-ac81-491c-a511-4f8543ac4b92
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component mul form 19371a71cdac: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component mul form 19371a71cdac
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component mul form 19371a71cdac construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component mul form 19371a71cdac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L119-L128

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_mul_form_19371a71cdac {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c)
    (t : MRing ι F) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) (b + c) (t * s) =
      weightedHomogeneousComponent (blockWeight ι) b t * s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«component_mul_form» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_mul_form_19371a71cdac
