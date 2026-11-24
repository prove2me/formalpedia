-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_colon_iff_a8700efb8128
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_colon_iff_a8700efb8128
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:58.460692+00:00
-- url     : https://prove2.me/theorems/cdacaa58-6602-45fb-8453-0c4449dcb34a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mem colon iff a8700efb8128: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mem colon iff a8700efb8128
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mem colon iff a8700efb8128 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration mem colon iff a8700efb8128 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L131-L133

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
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_colon_iff_a8700efb8128 {J : Ideal (MRing ι F)} {s f : MRing ι F} :
    f ∈ J.colon (Ideal.span {s}) ↔ f * s ∈ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«mem_colon_iff» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_colon_iff_a8700efb8128
