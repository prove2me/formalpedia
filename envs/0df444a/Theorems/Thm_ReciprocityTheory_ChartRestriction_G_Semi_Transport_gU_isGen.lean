-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_isGen
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_isGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:35.504884+00:00
-- url     : https://prove2.me/theorems/66cb5445-1e7a-49f0-94b1-23d3ddd71049
-- title:
--   Transport: g U is Gen
-- statement:
--   The Transport construction uses the g U is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L83-L87

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_isGen {L : LB X} {t : LB.Gen L} (ht : t.IsGen) {i j : L.ι} (x : X) (hi : x ∈ L.U i)
    (hj : x ∈ L.U j) :
    gU x hi (t.s i) = gU x (⟨hi, hj⟩ : x ∈ L.U i ⊓ L.U j) (L.g i j) * gU x hj (t.s j) := by sorry
