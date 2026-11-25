-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isPullHerm_tensor_86de3b803209
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isPullHerm_tensor_86de3b803209
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:42:38.027462+00:00
-- url     : https://prove2.me/theorems/94682277-2e1a-4b4f-966e-da1746ef1ce2
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Pull Herm tensor 86de3b803209: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Pull Herm ten
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Pull Herm tensor 86de3b803209 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Pull Herm tensor 86de3b803209 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L106-L113

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
omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isPullHerm_tensor_86de3b803209 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : HermLine ι}
    {A' B' : HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionIntegral».«isPullHerm_tensor» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isPullHerm_tensor_86de3b803209
