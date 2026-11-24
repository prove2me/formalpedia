-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_ne_zero_of_isChowFormCycle_98bd857a68c7
-- name    : P2M_GroundTheory_Heights__Heights_RecQOfRecursion_ne_zero_of_isChowFormCycle_98bd857a68c7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:57.693257+00:00
-- url     : https://prove2.me/theorems/0acdeea3-8e74-4d7d-8307-f3454a992b71
-- title:
--   P2 M Ground Theory Heights  Heights Rec QOf Recursion ne zero of is Chow Form Cycle 98bd857a68c7: P2 M Ground Theory Heights  Heights Rec QOf Recursion ne zero of is Chow Form Cycle 98bd857a68c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rec QOf Recursion ne zero of is Chow Form Cycle 98bd857a68c7 construction uses the P2 M Ground Theory Heights  Heights Rec QOf Recursion ne zero of is Chow Form Cycle 98bd857a68c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L25-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_FiniteSupportLogCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivSuppHorizontalArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_HeightMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion
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
noncomputable section
open GroundTheory.Heights₂.Heights.RecQOfRecursion
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RecQOfRecursion_ne_zero_of_isChowFormCycle_98bd857a68c7 {F : Type*} [Field F] {Z : ProjCycle F n} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) : f ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RecQOfRecursion».«ne_zero_of_isChowFormCycle» := P2M_GroundTheory_Heights__Heights_RecQOfRecursion_ne_zero_of_isChowFormCycle_98bd857a68c7
