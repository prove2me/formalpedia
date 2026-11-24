-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_isHomogeneous_of_multiHomog_9ab68c09e1f6
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_isHomogeneous_of_multiHomog_9ab68c09e1f6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:23.68586+00:00
-- url     : https://prove2.me/theorems/d52afa9a-2e25-45a8-8e18-7a42e281f898
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration is Homogeneous of multi Homog 9ab68c09e1f6: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration is Homogeneous of mult
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration is Homogeneous of multi Homog 9ab68c09e1f6 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration is Homogeneous of multi Homog 9ab68c09e1f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L80-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L80-L96

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_isHomogeneous_of_multiHomog_9ab68c09e1f6 {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (lexGrading ι F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«isHomogeneous_of_multiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_isHomogeneous_of_multiHomog_9ab68c09e1f6
