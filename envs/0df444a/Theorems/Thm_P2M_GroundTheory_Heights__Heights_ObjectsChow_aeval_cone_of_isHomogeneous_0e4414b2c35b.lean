-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_cone_of_isHomogeneous_0e4414b2c35b
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_cone_of_isHomogeneous_0e4414b2c35b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:09.703297+00:00
-- url     : https://prove2.me/theorems/29a499d1-3834-41bb-aa7b-c900cb970e2c
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow aeval cone of is Homogeneous 0e4414b2c35b: P2 M Ground Theory Heights  Heights Objects Chow aeval cone of is Homogeneous 0e4414b2c35b
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow aeval cone of is Homogeneous 0e4414b2c35b construction uses the P2 M Ground Theory Heights  Heights Objects Chow aeval cone of is Homogeneous 0e4414b2c35b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PClosedPointConeCoord.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PClosedPointConeCoord.lean#L11-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointConeCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PClosedPointConeCoord
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
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_cone_of_isHomogeneous_0e4414b2c35b {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n d : ℕ}
    (y : Fin n → Ω) {p : MvPolynomial (Fin n) F} (hp : p.IsHomogeneous d) :
    aeval (fun j => Polynomial.C (y j) * Polynomial.X) p =
      Polynomial.C (aeval y p) * Polynomial.X ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«aeval_cone_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_cone_of_isHomogeneous_0e4414b2c35b
