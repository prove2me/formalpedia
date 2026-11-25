-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_eq_span_28202021c411
-- name    : P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_eq_span_28202021c411
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:10.452729+00:00
-- url     : https://prove2.me/theorems/2dc15c13-cf50-4046-bb42-4e49b48891f8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal eq span 28202021c411: P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal eq span 28202021c411
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal eq span 28202021c411 construction uses the P2 M Ground Theory Heights  Heights Vertical Part Gauss fin Ideal eq span 28202021c411 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L94-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/FiniteSupportLogCoeffGaussNorm.lean#L94-L119

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

theorem P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_eq_span_28202021c411 {P : Ideal (MRing (PBlk n))} {S : Set (MRing (PBlk n))}
    (hS : P = Ideal.span S) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = Ideal.span (rename (blkEquiv n).symm '' S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VerticalPartGauss».«finIdeal_eq_span» := P2M_GroundTheory_Heights__Heights_VerticalPartGauss_finIdeal_eq_span_28202021c411
