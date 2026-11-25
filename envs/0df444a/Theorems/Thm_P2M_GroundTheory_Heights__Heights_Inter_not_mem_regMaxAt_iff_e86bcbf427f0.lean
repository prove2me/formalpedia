-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_not_mem_regMaxAt_iff_e86bcbf427f0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_not_mem_regMaxAt_iff_e86bcbf427f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:58.175999+00:00
-- url     : https://prove2.me/theorems/f8d0dfd6-9db0-4878-accb-07d49bd0206d
-- title:
--   P2 M Ground Theory Heights  Heights Inter not mem reg Max At iff e86bcbf427f0: P2 M Ground Theory Heights  Heights Inter not mem reg Max At iff e86bcbf427f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter not mem reg Max At iff e86bcbf427f0 construction uses the P2 M Ground Theory Heights  Heights Inter not mem reg Max At iff e86bcbf427f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L43-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean#L43-L59

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

theorem P2M_GroundTheory_Heights__Heights_Inter_not_mem_regMaxAt_iff_e86bcbf427f0 {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W)
    (hloc : IsLocalRing (locRing P W)) (x : regRing P) :
    x ∉ regMaxAt P W hW hPW hloc ↔
      ∃ z ∈ locRing P W, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«not_mem_regMaxAt_iff» := P2M_GroundTheory_Heights__Heights_Inter_not_mem_regMaxAt_iff_e86bcbf427f0
