-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_smul_of_isHomogeneous_01baa75c08b8
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_smul_of_isHomogeneous_01baa75c08b8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:20.160014+00:00
-- url     : https://prove2.me/theorems/bf8316e3-94d8-46b2-8f06-2b80e3511f31
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow aeval smul of is Homogeneous 01baa75c08b8: P2 M Ground Theory Heights  Heights Objects Chow aeval smul of is Homogeneous 01baa75c08b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow aeval smul of is Homogeneous 01baa75c08b8 construction uses the P2 M Ground Theory Heights  Heights Objects Chow aeval smul of is Homogeneous 01baa75c08b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowDegreeClosedPoint.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowDegreeClosedPoint.lean#L15-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointChartField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointConeCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIntChowFormExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowDegreeClosedPoint
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
open MvPolynomial Vertical Vertical.NormFormIrreducible

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_smul_of_isHomogeneous_01baa75c08b8 {F K : Type*} [Field F] [Field K] [Algebra F K] {n d : ℕ}
    {g : MvPolynomial (Fin n) F} (hg : g.IsHomogeneous d) (c : K) (y : Fin n → K) :
    aeval (fun j => c * y j) g = c ^ d * aeval y g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«aeval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_smul_of_isHomogeneous_01baa75c08b8
