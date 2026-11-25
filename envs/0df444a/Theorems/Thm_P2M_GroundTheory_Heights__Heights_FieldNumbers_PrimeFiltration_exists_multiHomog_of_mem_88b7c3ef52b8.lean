-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_multiHomog_of_mem_88b7c3ef52b8
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_multiHomog_of_mem_88b7c3ef52b8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:38.701551+00:00
-- url     : https://prove2.me/theorems/7473c055-82ff-4146-86b0-c02aed18e078
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists multi Homog of mem 88b7c3ef52b8: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists multi Homog of mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists multi Homog of mem 88b7c3ef52b8 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration exists multi Homog of mem 88b7c3ef52b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L111-L117

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_multiHomog_of_mem_88b7c3ef52b8 {s : MRing ι F} {m : Lex (Fin (Fintype.card K) → ℕ)}
    (hs : s ∈ lexGrading ι F m) (h0 : s ≠ 0) : ∃ c : K → ℕ, IsMultiHomog s c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«exists_multiHomog_of_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_multiHomog_of_mem_88b7c3ef52b8
