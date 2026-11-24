-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_1fa83b0aeb12
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_1fa83b0aeb12
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:45.653917+00:00
-- url     : https://prove2.me/theorems/828540b0-e54b-4088-9027-f9b52da8bb39
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex 1fa83b0aeb12: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex 1fa83b0aeb12
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex 1fa83b0aeb12 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration component lex 1fa83b0aeb12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L54-L58

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_1fa83b0aeb12 (f : MRing ι F) (b : K → ℕ) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) (lexEmb K b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«component_lex» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_1fa83b0aeb12
