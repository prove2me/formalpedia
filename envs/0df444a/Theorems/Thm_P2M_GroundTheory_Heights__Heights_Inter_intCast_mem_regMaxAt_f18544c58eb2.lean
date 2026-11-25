-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_intCast_mem_regMaxAt_f18544c58eb2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_intCast_mem_regMaxAt_f18544c58eb2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:31.158485+00:00
-- url     : https://prove2.me/theorems/59918374-44d7-447b-85f9-518c1623ebf3
-- title:
--   P2 M Ground Theory Heights  Heights Inter int Cast mem reg Max At f18544c58eb2: P2 M Ground Theory Heights  Heights Inter int Cast mem reg Max At f18544c58eb2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter int Cast mem reg Max At f18544c58eb2 construction uses the P2 M Ground Theory Heights  Heights Inter int Cast mem reg Max At f18544c58eb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L61-L70

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

theorem P2M_GroundTheory_Heights__Heights_Inter_intCast_mem_regMaxAt_f18544c58eb2 (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)} (hPp : P.IsPrime)
    (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) {n : ℤ} (hn : C n ∈ W) :
    (n : regRing P) ∈ regMaxAt P W hW hPW hloc := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«intCast_mem_regMaxAt» := P2M_GroundTheory_Heights__Heights_Inter_intCast_mem_regMaxAt_f18544c58eb2
