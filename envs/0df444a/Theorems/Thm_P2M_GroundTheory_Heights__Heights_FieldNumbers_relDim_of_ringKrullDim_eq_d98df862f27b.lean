-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_of_ringKrullDim_eq_d98df862f27b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_of_ringKrullDim_eq_d98df862f27b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:11.484371+00:00
-- url     : https://prove2.me/theorems/fb64ac6a-7cc0-4100-bfba-a62d65749164
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rel Dim of ring Krull Dim eq d98df862f27b: P2 M Ground Theory Heights  Heights Field Numbers rel Dim of ring Krull Dim eq d98df862f27b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rel Dim of ring Krull Dim eq d98df862f27b construction uses the P2 M Ground Theory Heights  Heights Field Numbers rel Dim of ring Krull Dim eq d98df862f27b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPrincipalDegree.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPrincipalDegree.lean#L20-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree
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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_of_ringKrullDim_eq_d98df862f27b (I : Ideal (MRing ι F)) (d : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = (d : WithBot ℕ∞)) :
    relDim I = (((d : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«relDim_of_ringKrullDim_eq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_of_ringKrullDim_eq_d98df862f27b
