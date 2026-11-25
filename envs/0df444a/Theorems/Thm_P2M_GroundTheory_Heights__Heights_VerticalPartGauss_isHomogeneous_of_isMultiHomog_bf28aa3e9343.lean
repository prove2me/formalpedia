-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isHomogeneous_of_isMultiHomog_bf28aa3e9343
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isHomogeneous_of_isMultiHomog_bf28aa3e9343
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:28.395931+00:00
-- url     : https://prove2.me/theorems/1fead6d0-6acd-470b-adfc-143a658ed101
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss is Homogeneous of is Multi Homog bf28aa3e9343: P2 M Ground Theory Heights  Heights Vertical Part Gauss is Homogeneous of is Multi Homog bf28aa3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss is Homogeneous of is Multi Homog bf28aa3e9343 construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss is Homogeneous of is Multi Homog bf28aa3e9343 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L84-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.VerticalPartGauss
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isHomogeneous_of_isMultiHomog_bf28aa3e9343 {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    (map (Int.castRingHom ℚ) (rename (blkEquiv n).symm s)).IsHomogeneous (a ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«isHomogeneous_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isHomogeneous_of_isMultiHomog_bf28aa3e9343
