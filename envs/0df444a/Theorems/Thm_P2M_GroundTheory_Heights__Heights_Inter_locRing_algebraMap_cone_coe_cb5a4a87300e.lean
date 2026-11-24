-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locRing_algebraMap_cone_coe_cb5a4a87300e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_locRing_algebraMap_cone_coe_cb5a4a87300e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:09.754803+00:00
-- url     : https://prove2.me/theorems/82349550-5a72-4c78-aaa5-affd42448368
-- title:
--   P2 M Ground Theory Heights  Heights Inter loc Ring algebra Map cone coe cb5a4a87300e: P2 M Ground Theory Heights  Heights Inter loc Ring algebra Map cone coe cb5a4a87300e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter loc Ring algebra Map cone coe cb5a4a87300e construction uses the P2 M Ground Theory Heights  Heights Inter loc Ring algebra Map cone coe cb5a4a87300e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PrimeComplMapLeNonZeroDivisorsQuot.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PrimeComplMapLeNonZeroDivisorsQuot.lean#L51-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_locRing_algebraMap_cone_coe_cb5a4a87300e (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W)
    (x : locRing P W) :
    ((algebraMap (locRing P W) (coneLocRing P W hPW) x : coneLocRing P W hPW) :
      FractionRing (MRing ι ⧸ P)) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«locRing».«algebraMap_cone_coe» := P2M_GroundTheory_Heights__Heights_Inter_locRing_algebraMap_cone_coe_cb5a4a87300e
