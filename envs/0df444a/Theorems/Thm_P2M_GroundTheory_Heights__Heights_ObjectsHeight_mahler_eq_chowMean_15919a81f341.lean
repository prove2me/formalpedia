-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:18.943882+00:00
-- url     : https://prove2.me/theorems/dea43c35-a48e-4a5a-a579-aafca0db6b79
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height mahler eq chow Mean 15919a81f341: P2 M Ground Theory Heights  Heights Objects Height mahler eq chow Mean 15919a81f341
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height mahler eq chow Mean 15919a81f341 construction uses the P2 M Ground Theory Heights  Heights Objects Height mahler eq chow Mean 15919a81f341 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L321-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L321-L325

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341 (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (h : HermNorm n)
    (hh : ∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) (f : MvPolynomial (Fin k × Fin n) ℂ) :
    mahler h k f = IndefiniteRowSideFullHecke.ArithBezout.chowMean S k f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«mahler_eq_chowMean» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_eq_chowMean_15919a81f341
