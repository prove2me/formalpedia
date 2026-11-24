-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:35.237766+00:00
-- url     : https://prove2.me/theorems/48108c41-f69b-49c9-a56e-9153a72a0ae3
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Height 9bf18eb67ddd: P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Height 9bf18eb67ddd
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Height 9bf18eb67ddd construction uses the P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Height 9bf18eb67ddd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L372-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L372-L389

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd {e δ : ℕ} (H : ArchData ℚ n) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S) (hH : ∀ σ u, (H.normAt σ).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ) :
    chowHt H (e + 1) δ f = IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«chowHt_eq_chowHeight» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd
