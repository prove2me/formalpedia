-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_div
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:54.38494+00:00
-- url     : https://prove2.me/theorems/a641b711-70ea-4a62-a5f2-7f7b68e1a46b
-- title:
--   Transport: g U div
-- statement:
--   The Transport construction uses the g U div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L89-L95

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_div (B A : LB X) (p q : (LB.div B A).ι) (x : X) (hp : x ∈ (LB.div B A).U p)
    (hq : x ∈ (LB.div B A).U q) :
    gU x (⟨hp, hq⟩ : x ∈ (LB.div B A).U p ⊓ (LB.div B A).U q) ((LB.div B A).g p q) =
      gU x (⟨hp.1, hq.1⟩ : x ∈ B.U p.1 ⊓ B.U q.1) (B.g p.1 q.1) *
        (gU x (⟨hp.2, hq.2⟩ : x ∈ A.U p.2 ⊓ A.U q.2) (A.g p.2 q.2))⁻¹ := by sorry
