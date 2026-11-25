-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraMap_injective_of_horizontal_87dc56f4d22c
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraMap_injective_of_horizontal_87dc56f4d22c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:50.640909+00:00
-- url     : https://prove2.me/theorems/7e95225d-a113-5ed1-932b-bdae078fb763
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility algebra Map injective of horizontal 87dc56f4d22c: P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibilit
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility algebra Map injective of horizontal 87dc56f4d22c construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility algebra Map injective of horizontal 87dc56f4d22c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncomp.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncomp.lean#L37-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncompTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIncomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncomp
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter.PointVertical
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraMap_injective_of_horizontal_87dc56f4d22c (I : Ideal (MRing ι)) (h : IsHorizontal I) :
    Function.Injective (algebraMap ℤ (MRing ι ⧸ I)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreIncompressibility».«algebraMap_injective_of_horizontal» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraMap_injective_of_horizontal_87dc56f4d22c
