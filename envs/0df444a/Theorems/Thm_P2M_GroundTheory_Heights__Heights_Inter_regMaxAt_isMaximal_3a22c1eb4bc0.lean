-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regMaxAt_isMaximal_3a22c1eb4bc0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regMaxAt_isMaximal_3a22c1eb4bc0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:21.952513+00:00
-- url     : https://prove2.me/theorems/2e025bc9-165b-4655-b6b5-1f7b3f34ae89
-- title:
--   P2 M Ground Theory Heights  Heights Inter reg Max At is Maximal 3a22c1eb4bc0: P2 M Ground Theory Heights  Heights Inter reg Max At is Maximal 3a22c1eb4bc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter reg Max At is Maximal 3a22c1eb4bc0 construction uses the P2 M Ground Theory Heights  Heights Inter reg Max At is Maximal 3a22c1eb4bc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L72-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L72-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regMaxAt_isMaximal_3a22c1eb4bc0 (hO : RegularityOrder.Statement) (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    (regMaxAt P W hW hPW hloc).IsMaximal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regMaxAt_isMaximal» := P2M_GroundTheory_Heights__Heights_Inter_regMaxAt_isMaximal_3a22c1eb4bc0
