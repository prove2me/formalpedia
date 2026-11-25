-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_PFCoord_of_found_98a9f87ddae8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_PFCoord_of_found_98a9f87ddae8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:38.299032+00:00
-- url     : https://prove2.me/theorems/4ef2ae2c-5d4e-4235-b4fa-637b134b47a2
-- title:
--   P2 M Ground Theory Heights  Heights Targets PFCoord of found 98a9f87ddae8: P2 M Ground Theory Heights  Heights Targets PFCoord of found 98a9f87ddae8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets PFCoord of found 98a9f87ddae8 construction uses the P2 M Ground Theory Heights  Heights Targets PFCoord of found 98a9f87ddae8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFCoord.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFCoord.lean#L13-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordFibreDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFCoord
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Targets_PFCoord_of_found_98a9f87ddae8 (hGD : GenDegStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hGF : GenFibreExistsStatement) (hFD : FibreDimStatement) (hCF : CoordFibreDeg.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«PFCoord».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_PFCoord_of_found_98a9f87ddae8
