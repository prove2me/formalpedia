-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ae_eval_ne_zero_511da99b05d4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ae_eval_ne_zero_511da99b05d4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:45.334269+00:00
-- url     : https://prove2.me/theorems/78e967bf-beda-48ca-a9ac-5186a4990356
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral ae eval ne zero 511da99b05d4: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral ae eval ne zero 511d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral ae eval ne zero 511da99b05d4 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral ae eval ne zero 511da99b05d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L21-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsIntegralLogNormRat
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
  ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ae_eval_ne_zero_511da99b05d4 {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) {h : MRing ι} (hh : ∃ a, IsMultiHomog h a)
    (hhP : h ∉ P) :
    ∀ᵐ y : Fin e → ℂ, ∀ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y →
      eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionIntegral».«ae_eval_ne_zero» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ae_eval_ne_zero_511da99b05d4
