-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_iso
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:45.205645+00:00
-- url     : https://prove2.me/theorems/af4035e6-cc6c-4e57-81a2-99f4ef2fcf87
-- title:
--   Transport: g U iso
-- statement:
--   The Transport construction uses the g U iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L171-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L171-L178

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
variable {A B C : LB X}

theorem ReciprocityTheory.ChartRestriction.G.Semi.Transport.gU_iso (w : LB.Iso A B) (hw : w.IsGen) (p p' : B.ι) (q q' : A.ι) (x : X)
    (h : x ∈ A.U q ⊓ B.U p) (h' : x ∈ A.U q' ⊓ B.U p') :
    gU x (le_divU p q h) (w.s (pq p q)) =
      gU x (⟨h.2, h'.2⟩ : x ∈ B.U p ⊓ B.U p') (B.g p p') *
        (gU x (⟨h.1, h'.1⟩ : x ∈ A.U q ⊓ A.U q') (A.g q q'))⁻¹ * gU x (le_divU p' q' h') (w.s (pq p' q')) := by sorry
