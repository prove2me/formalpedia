-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regToLoc_apply_b3e64aab997c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regToLoc_apply_b3e64aab997c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:20.866571+00:00
-- url     : https://prove2.me/theorems/43627325-529c-4891-87eb-f7a59f673433
-- title:
--   P2 M Ground Theory Heights  Heights Inter reg To Loc apply b3e64aab997c: P2 M Ground Theory Heights  Heights Inter reg To Loc apply b3e64aab997c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter reg To Loc apply b3e64aab997c construction uses the P2 M Ground Theory Heights  Heights Inter reg To Loc apply b3e64aab997c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L30-L32

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regToLoc_apply_b3e64aab997c {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    regToLoc P W hW hPW x = ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regToLoc_apply» := P2M_GroundTheory_Heights__Heights_Inter_regToLoc_apply_b3e64aab997c
