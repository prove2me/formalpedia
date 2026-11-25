-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_GluingInclusion_cm_nat_apply
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.cm_nat_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:44.352788+00:00
-- url     : https://prove2.me/theorems/581d2b97-6572-4379-b4b0-3ce62466392b
-- title:
--   Gluing Inclusion: cm nat apply
-- statement:
--   The Gluing Inclusion construction uses the cm nat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L51-L54

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
variable (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (x : Multiplicative X),
    φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))
include hnat

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.cm_nat_apply {V₁ V₂ : B.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (p : AddMonoidAlgebra Γ(B, V₂) X) :
    cm q φ V₁ h₁ (AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE h).op).hom p) =
      (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (cm q φ V₂ h₂ p) := by sorry
