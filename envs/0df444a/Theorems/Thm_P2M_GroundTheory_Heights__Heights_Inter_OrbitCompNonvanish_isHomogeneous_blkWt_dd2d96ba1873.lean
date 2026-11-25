-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isHomogeneous_blkWt_dd2d96ba1873
-- name    : P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isHomogeneous_blkWt_dd2d96ba1873
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:17.143396+00:00
-- url     : https://prove2.me/theorems/50740755-e8ea-43c0-a5fd-badfb175bada
-- title:
--   P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish is Homogeneous blk Wt dd2d96ba1873: P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish is Homogeneous blk Wt dd2d96ba1873
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish is Homogeneous blk Wt dd2d96ba1873 construction uses the P2 M Ground Theory Heights  Heights Inter Orbit Comp Nonvanish is Homogeneous blk Wt dd2d96ba1873 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/POrbitCompNonvanish.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/POrbitCompNonvanish.lean#L17-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_POrbitCompNonvanish
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isHomogeneous_blkWt_dd2d96ba1873 {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blkWt (ι := ι))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«OrbitCompNonvanish».«isHomogeneous_blkWt» := P2M_GroundTheory_Heights__Heights_Inter_OrbitCompNonvanish_isHomogeneous_blkWt_dd2d96ba1873
