-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isPrime_21e151008f95
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isPrime_21e151008f95
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:24.739358+00:00
-- url     : https://prove2.me/theorems/fcc9c846-a6f8-43e7-bbfd-11d668d5d904
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal is Prime 21e151008f95: P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal is Prime 21e151008f95
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal is Prime 21e151008f95 construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal is Prime 21e151008f95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L72-L76

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isPrime_21e151008f95 {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (genericIdeal P).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«genericIdeal_isPrime» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_isPrime_21e151008f95
