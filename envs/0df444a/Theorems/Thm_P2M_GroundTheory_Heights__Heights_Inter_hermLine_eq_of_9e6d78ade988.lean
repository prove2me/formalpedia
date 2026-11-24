-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_hermLine_eq_of_9e6d78ade988
-- name    : P2M_GroundTheory_Heights__Heights_Inter_hermLine_eq_of_9e6d78ade988
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:57.543801+00:00
-- url     : https://prove2.me/theorems/7f476b32-5138-4517-a630-144f1f9f984a
-- title:
--   P2 M Ground Theory Heights  Heights Inter herm Line eq of 9e6d78ade988: P2 M Ground Theory Heights  Heights Inter herm Line eq of 9e6d78ade988
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter herm Line eq of 9e6d78ade988 construction uses the P2 M Ground Theory Heights  Heights Inter herm Line eq of 9e6d78ade988 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L16-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_hermLine_eq_of_9e6d78ade988 {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«hermLine_eq_of» := P2M_GroundTheory_Heights__Heights_Inter_hermLine_eq_of_9e6d78ade988
