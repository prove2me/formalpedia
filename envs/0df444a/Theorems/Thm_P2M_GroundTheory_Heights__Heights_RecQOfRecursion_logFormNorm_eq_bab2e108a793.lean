-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RecQOfRecursion_logFormNorm_eq_bab2e108a793
-- name    : P2M_GroundTheory_Heights__Heights_RecQOfRecursion_logFormNorm_eq_bab2e108a793
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:55.847889+00:00
-- url     : https://prove2.me/theorems/6a9d7089-67fb-43e4-8edc-6e4cb31e7c78
-- title:
--   P2 M Ground Theory Heights  Heights Rec QOf Recursion log Form Norm eq bab2e108a793: P2 M Ground Theory Heights  Heights Rec QOf Recursion log Form Norm eq bab2e108a793
-- statement:
--   The P2 M Ground Theory Heights  Heights Rec QOf Recursion log Form Norm eq bab2e108a793 construction uses the P2 M Ground Theory Heights  Heights Rec QOf Recursion log Form Norm eq bab2e108a793 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecQOfRecursion.lean#L52-L57

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

theorem P2M_GroundTheory_Heights__Heights_RecQOfRecursion_logFormNorm_eq_bab2e108a793 (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℤ) :
    IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS (fun i => (u i : ℂ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.logNorm (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RecQOfRecursion».«logFormNorm_eq» := P2M_GroundTheory_Heights__Heights_RecQOfRecursion_logFormNorm_eq_bab2e108a793
