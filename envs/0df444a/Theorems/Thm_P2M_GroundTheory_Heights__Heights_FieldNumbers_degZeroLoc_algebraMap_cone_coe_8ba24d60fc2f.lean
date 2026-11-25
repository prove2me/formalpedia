-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_cone_coe_8ba24d60fc2f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_cone_coe_8ba24d60fc2f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:12:48.101217+00:00
-- url     : https://prove2.me/theorems/36d61537-5cb2-4c97-8d26-0fb3d71288d3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map cone coe 8ba24d60fc2f: P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map cone coe 8ba24d60fc2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map cone coe 8ba24d60fc2f construction uses the P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc algebra Map cone coe 8ba24d60fc2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsConeLocalFlat.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsConeLocalFlat.lean#L59-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_cone_coe_8ba24d60fc2f (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (x : degZeroLoc P {W}) :
    ((algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) x : coneLocal P W hPW) :
      FractionRing (MRing ι F ⧸ P)) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«degZeroLoc».«algebraMap_cone_coe» := P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_cone_coe_8ba24d60fc2f
