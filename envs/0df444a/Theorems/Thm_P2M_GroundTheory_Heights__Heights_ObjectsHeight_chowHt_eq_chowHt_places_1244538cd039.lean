-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHt_places_1244538cd039
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHt_places_1244538cd039
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:12.76532+00:00
-- url     : https://prove2.me/theorems/6c3d8b77-57d0-424d-b723-cfd811c57a40
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Ht places 1244538cd039: P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Ht places 1244538cd039
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Ht places 1244538cd039 construction uses the P2 M Ground Theory Heights  Heights Objects Height chow Ht eq chow Ht places 1244538cd039 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L480-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L480-L499

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHt_places_1244538cd039 {K : Type} [Field K] [NumberField K] {e δ : ℕ} (H : ArchData K n)
    (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hS : ∀ w, IsUnit (S w))
    (hH : ∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (S w) u)
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) :
    chowHt H (e + 1) δ f =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«chowHt_eq_chowHt_places» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHt_places_1244538cd039
