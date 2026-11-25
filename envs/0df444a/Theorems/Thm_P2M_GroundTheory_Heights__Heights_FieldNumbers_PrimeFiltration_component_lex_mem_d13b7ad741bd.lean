-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_mem_d13b7ad741bd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_mem_d13b7ad741bd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:13.929706+00:00
-- url     : https://prove2.me/theorems/dda51449-2f56-536b-99bf-844559484a4a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex mem d13b7ad741bd: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex mem d13b7ad741bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex mem d13b7ad741bd construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex mem d13b7ad741bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L67-L76

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_mem_d13b7ad741bd {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {f : MRing ι F}
    (hf : f ∈ I) (m : Lex (Fin (Fintype.card K) → ℕ)) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) m f ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«component_lex_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_mem_d13b7ad741bd
