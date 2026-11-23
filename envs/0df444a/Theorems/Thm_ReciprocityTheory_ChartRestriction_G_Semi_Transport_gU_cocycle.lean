-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_cocycle
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_cocycle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:12.029183+00:00
-- url     : https://prove2.me/theorems/197d6415-c073-429a-940b-7bf03b0567f4
-- title:
--   Transport: g U cocycle
-- statement:
--   The Transport construction uses the g U cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L71-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_cocycle {L : LB X} (hL : L.IsLB) {i j k : L.ι} (x : X) (hi : x ∈ L.U i) (hj : x ∈ L.U j)
    (hk : x ∈ L.U k) :
    gU x (⟨hi, hj⟩ : x ∈ L.U i ⊓ L.U j) (L.g i j) * gU x (⟨hj, hk⟩ : x ∈ L.U j ⊓ L.U k) (L.g j k) =
      gU x (⟨hi, hk⟩ : x ∈ L.U i ⊓ L.U k) (L.g i k) := by sorry
