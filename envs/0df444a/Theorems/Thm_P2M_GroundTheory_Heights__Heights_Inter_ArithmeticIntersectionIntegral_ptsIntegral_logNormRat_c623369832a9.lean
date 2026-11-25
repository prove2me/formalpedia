-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ptsIntegral_logNormRat_c623369832a9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ptsIntegral_logNormRat_c623369832a9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:10.586648+00:00
-- url     : https://prove2.me/theorems/ee5448cc-948d-4b1a-a746-e563dd46eab6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pts Integral log Norm Rat c623369832a9: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pts Integr
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pts Integral log Norm Rat c623369832a9 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pts Integral log Norm Rat c623369832a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L38-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L38-L76

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ptsIntegral_logNormRat_c623369832a9 (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    {L : Fin n → HermLine ι} {A B : HermLine ι} {f g : MRing ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hf : IsSectionOn P (A.tensor B) f) (hg : IsSectionOn P B g) :
    ptsIntegral P (pot L) (logNormRat A f g) =
      ptsIntegral P (pot L) (logNorm (A.tensor B) f) - ptsIntegral P (pot L) (logNorm B g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionIntegral».«ptsIntegral_logNormRat» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_ptsIntegral_logNormRat_c623369832a9
