-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isProjPrime_genericIdeal_2708c8f68489
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isProjPrime_genericIdeal_2708c8f68489
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:04.655415+00:00
-- url     : https://prove2.me/theorems/5b7c364b-4259-4109-9771-a35a6a37fe12
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss is Proj Prime generic Ideal 2708c8f68489: P2 M Ground Theory Heights  Heights Vertical Part Gauss is Proj Prime generic Ideal 2708c8f68489
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss is Proj Prime generic Ideal 2708c8f68489 construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss is Proj Prime generic Ideal 2708c8f68489 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L145-L147

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isProjPrime_genericIdeal_2708c8f68489 {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsProjPrime (genericIdeal P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«isProjPrime_genericIdeal» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_isProjPrime_genericIdeal_2708c8f68489
