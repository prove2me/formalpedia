-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_divCycle_apply_70c37bfa12bc
-- name    : P2M_GroundTheory_Heights__Heights_RecQOfRecursion_divCycle_apply_70c37bfa12bc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:52.084747+00:00
-- url     : https://prove2.me/theorems/e9296a4c-9731-4bbc-9894-e7ba9b40b07e
-- title:
--   P2 M Ground Theory Heights  Heights Rec QOf Recursion div Cycle apply 70c37bfa12bc: P2 M Ground Theory Heights  Heights Rec QOf Recursion div Cycle apply 70c37bfa12bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Rec QOf Recursion div Cycle apply 70c37bfa12bc construction uses the P2 M Ground Theory Heights  Heights Rec QOf Recursion div Cycle apply 70c37bfa12bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L61-L63

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_RecQOfRecursion_divCycle_apply_70c37bfa12bc (P : Ideal (MRing (PBlk n))) (s : MRing (PBlk n)) (W : Ideal (MRing (PBlk n))) :
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W = if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RecQOfRecursion».«divCycle_apply» := P2M_GroundTheory_Heights__Heights_RecQOfRecursion_divCycle_apply_70c37bfa12bc
