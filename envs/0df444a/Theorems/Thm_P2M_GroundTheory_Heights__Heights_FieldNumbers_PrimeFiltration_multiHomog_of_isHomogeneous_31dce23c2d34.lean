-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_of_isHomogeneous_31dce23c2d34
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_of_isHomogeneous_31dce23c2d34
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:04.443838+00:00
-- url     : https://prove2.me/theorems/a601c703-f44f-4bd8-8fda-81a8c67371ea
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog of is Homogeneous 31dce23c2d34: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog of is Homo
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog of is Homogeneous 31dce23c2d34 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration multi Homog of is Homogeneous 31dce23c2d34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L98-L103

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_of_isHomogeneous_31dce23c2d34 {I : Ideal (MRing ι F)}
    (h : I.IsHomogeneous (lexGrading ι F)) : IsMultiHomogIdeal I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«multiHomog_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_of_isHomogeneous_31dce23c2d34
