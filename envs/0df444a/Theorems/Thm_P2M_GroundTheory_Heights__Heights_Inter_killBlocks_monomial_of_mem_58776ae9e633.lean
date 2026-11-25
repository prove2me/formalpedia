-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_monomial_of_mem_58776ae9e633
-- name    : P2M_GroundTheory_Heights__Heights_Inter_killBlocks_monomial_of_mem_58776ae9e633
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:01.568178+00:00
-- url     : https://prove2.me/theorems/f6c578bc-b811-5a79-8a27-5b2475a057d8
-- title:
--   P2 M Ground Theory Heights  Heights Inter kill Blocks monomial of mem 58776ae9e633: P2 M Ground Theory Heights  Heights Inter kill Blocks monomial of mem 58776ae9e633
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter kill Blocks monomial of mem 58776ae9e633 construction uses the P2 M Ground Theory Heights  Heights Inter kill Blocks monomial of mem 58776ae9e633 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L37-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_killBlocks_monomial_of_mem_58776ae9e633 (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (p : Σ k, ι k)
    (hp : p ∈ m.support) (hS : p.1 ∈ S) : killBlocks S (monomial m c : MRing ι) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«killBlocks_monomial_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_killBlocks_monomial_of_mem_58776ae9e633
