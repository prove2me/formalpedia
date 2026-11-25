-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_degreeOfFamily_linearCombination
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily_linearCombination
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:40.898317+00:00
-- url     : https://prove2.me/theorems/b958e1df-4ede-43ae-a57e-4d3084df7b63
-- title:
--   Geometry Of Numbers Theory: degree Of Family linear Combination
-- statement:
--   The Geometry Of Numbers Theory construction uses the degree Of Family linear Combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStB.lean#L100-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStB.lean#L100-L147

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily_linearCombination (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (g : Matrix (Fin r) (Fin r) (𝓞 K))
    (hv' : LinearIndependent K (fun j => ∑ i, g i j • v i))
    (hvE : Submodule.span (𝓞 K) (Set.range v) ≤ E)
    (hne : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0) :
    degreeOfFamily h E (fun j => ∑ i, g i j • v i) = degreeOfFamily h E v := by sorry
