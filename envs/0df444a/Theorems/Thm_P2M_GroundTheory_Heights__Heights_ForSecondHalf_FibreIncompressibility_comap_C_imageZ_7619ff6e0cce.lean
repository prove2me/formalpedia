-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_comap_C_imageZ_7619ff6e0cce
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_comap_C_imageZ_7619ff6e0cce
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:00.491949+00:00
-- url     : https://prove2.me/theorems/09a4a153-1719-466f-894c-4aa2de18d680
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility comap C image Z 7619ff6e0cce: P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility comap C image Z 76
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility comap C image Z 7619ff6e0cce construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility comap C image Z 7619ff6e0cce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncomp.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncomp.lean#L48-L51

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
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_comap_C_imageZ_7619ff6e0cce (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    (imageZ v W').comap (C : ℤ →+* MRing ι) = W'.comap (C : ℤ →+* MRing ι') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreIncompressibility».«comap_C_imageZ» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_comap_C_imageZ_7619ff6e0cce
