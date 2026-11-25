-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCenterMemIff_weightedHomogeneousComponent_X_mul_0b047dbd7110
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCenterMemIff_weightedHomogeneousComponent_X_mul_0b047dbd7110
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:13.687315+00:00
-- url     : https://prove2.me/theorems/96b6fc4a-35d9-4120-85ee-8a2a67fef50b
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Center Mem Iff weighted Homogeneous Component X mul 0b047dbd7110: P2 M Ground Theory Heights  Heights Orbit Center Mem Iff weighted Homogeneous Component X mu
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Center Mem Iff weighted Homogeneous Component X mul 0b047dbd7110 construction uses the P2 M Ground Theory Heights  Heights Orbit Center Mem Iff weighted Homogeneous Component X mul 0b047dbd7110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterMemIff.lean#L15-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterMemIff.lean#L15-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterMemIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights.OrbitCenterMemIff
variable {ι : Type} [DecidableEq ι] {n : ι → ℕ}
open Classical

theorem P2M_GroundTheory_Heights__Heights_OrbitCenterMemIff_weightedHomogeneousComponent_X_mul_0b047dbd7110 (j : Coord n) (G : MvPolynomial (Coord n) ℤ)
    (e : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) e (X j * G) =
      if coordDeg n j ≤ e then X j * weightedHomogeneousComponent (coordDeg n) (e - coordDeg n j) G
      else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCenterMemIff».«weightedHomogeneousComponent_X_mul» := P2M_GroundTheory_Heights__Heights_OrbitCenterMemIff_weightedHomogeneousComponent_X_mul_0b047dbd7110
