-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_dim_add_card_le_d24c209910fd
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_dim_add_card_le_d24c209910fd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:56.537327+00:00
-- url     : https://prove2.me/theorems/2001a519-f651-4d3d-b140-78db27b433ef
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility dim add card le d24c209910fd: P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility dim add card le d2
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility dim add card le d24c209910fd construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility dim add card le d24c209910fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncomp.lean#L53-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncomp.lean#L53-L110

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

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_dim_add_card_le_d24c209910fd {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W' : Ideal (MRing ι')} (hW' : IsMultiProjPrime W') :
    ringKrullDim (MRing ι ⧸ imageZ v W') + (Fintype.card (FibreBlock κ) : WithBot ℕ∞) ≤
      ringKrullDim (MRing ι' ⧸ W') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreIncompressibility».«dim_add_card_le» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_dim_add_card_le_d24c209910fd
