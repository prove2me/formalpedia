-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_isPrime_530e89cd1eaf
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_isPrime_530e89cd1eaf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:39.759864+00:00
-- url     : https://prove2.me/theorems/82b34a7a-b382-45ce-9e2f-6d266821855e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal is Prime 530e89cd1eaf: P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal is Prime 530e89cd1eaf
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal is Prime 530e89cd1eaf construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal is Prime 530e89cd1eaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L43-L47

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_isPrime_530e89cd1eaf {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«finIdeal_isPrime» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_isPrime_530e89cd1eaf
