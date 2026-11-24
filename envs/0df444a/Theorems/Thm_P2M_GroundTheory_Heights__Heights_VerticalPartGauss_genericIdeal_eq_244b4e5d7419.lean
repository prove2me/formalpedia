-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_eq_244b4e5d7419
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_eq_244b4e5d7419
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:16.487139+00:00
-- url     : https://prove2.me/theorems/3968b699-9f1a-46eb-b2d7-3ad06c943839
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal eq 244b4e5d7419: P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal eq 244b4e5d7419
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal eq 244b4e5d7419 construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss generic Ideal eq 244b4e5d7419 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L37-L41

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_eq_244b4e5d7419 (P : Ideal (MRing (PBlk n))) :
    genericIdeal P = (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
      (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«genericIdeal_eq» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_genericIdeal_eq_244b4e5d7419
