-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_exists_C_mul_of_isChowForm_6628fc869e62
-- name    : P2M_GroundTheory_Heights__Heights_RecQOfRecursion_exists_C_mul_of_isChowForm_6628fc869e62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:03.540272+00:00
-- url     : https://prove2.me/theorems/02198c09-bc3c-40a7-8209-6bfd1b4cb6c3
-- title:
--   P2 M Ground Theory Heights  Heights Rec QOf Recursion exists C mul of is Chow Form 6628fc869e62: P2 M Ground Theory Heights  Heights Rec QOf Recursion exists C mul of is Chow Form 6628fc869e62
-- statement:
--   The P2 M Ground Theory Heights  Heights Rec QOf Recursion exists C mul of is Chow Form 6628fc869e62 construction uses the P2 M Ground Theory Heights  Heights Rec QOf Recursion exists C mul of is Chow Form 6628fc869e62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L31-L40

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

theorem P2M_GroundTheory_Heights__Heights_RecQOfRecursion_exists_C_mul_of_isChowForm_6628fc869e62 {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f g : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (hg : IsChowForm I k g) :
    ∃ r : F, r ≠ 0 ∧ g = C r * f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RecQOfRecursion».«exists_C_mul_of_isChowForm» := P2M_GroundTheory_Heights__Heights_RecQOfRecursion_exists_C_mul_of_isChowForm_6628fc869e62
