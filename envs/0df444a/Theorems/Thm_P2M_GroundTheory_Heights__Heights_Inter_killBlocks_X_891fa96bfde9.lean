-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_X_891fa96bfde9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_killBlocks_X_891fa96bfde9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:56.413842+00:00
-- url     : https://prove2.me/theorems/8fa6649c-64ce-4a3f-ae5b-8ac8ae140f94
-- title:
--   P2 M Ground Theory Heights  Heights Inter kill Blocks X 891fa96bfde9: P2 M Ground Theory Heights  Heights Inter kill Blocks X 891fa96bfde9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter kill Blocks X 891fa96bfde9 construction uses the P2 M Ground Theory Heights  Heights Inter kill Blocks X 891fa96bfde9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean#L22-L24

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_killBlocks_X_891fa96bfde9 (S : Set K) (p : Σ k, ι k) :
    killBlocks S (X p : MRing ι) = if p.1 ∈ S then 0 else X p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«killBlocks_X» := P2M_GroundTheory_Heights__Heights_Inter_killBlocks_X_891fa96bfde9
