-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_GluingInclusion_app_res
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.app_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:56.08166+00:00
-- url     : https://prove2.me/theorems/25ab9d8c-fe4c-5bfb-a494-44ae61f42bee
-- title:
--   Gluing Inclusion: app res
-- statement:
--   The Gluing Inclusion construction uses the app res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L20-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_SurjOfCover
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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion
variable {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
  (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
omit [AddCommMonoid X]

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.app_res {V₁ V₂ : B.Opens} (h : V₁ ≤ V₂) (c : Γ(B, V₂)) :
    (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom ((q.app V₂).hom c) =
      (q.app V₁).hom ((B.presheaf.map (homOfLE h).op).hom c) := by sorry
