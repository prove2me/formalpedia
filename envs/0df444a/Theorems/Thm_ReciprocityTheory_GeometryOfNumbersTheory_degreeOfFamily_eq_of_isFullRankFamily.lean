-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_degreeOfFamily_eq_of_isFullRankFamily
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily_eq_of_isFullRankFamily
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:45.488045+00:00
-- url     : https://prove2.me/theorems/03a582ca-7ae2-57c2-809d-bee9e26e4e04
-- title:
--   Geometry Of Numbers Theory: degree Of Family eq of is Full Rank Family
-- statement:
--   The Geometry Of Numbers Theory construction uses the degree Of Family eq of is Full Rank Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStB.lean#L149-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStB.lean#L149-L188

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily_eq_of_isFullRankFamily (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ}
    {v v' : Fin r → V} (hv : IsFrame K E v) (hv' : IsFrame K E v') :
    degreeOfFamily h E v = degreeOfFamily h E v' := by sorry
