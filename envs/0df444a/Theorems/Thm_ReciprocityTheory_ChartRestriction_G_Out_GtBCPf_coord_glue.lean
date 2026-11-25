-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_coord_glue
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.coord_glue
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:14.665551+00:00
-- url     : https://prove2.me/theorems/8893b738-8d6d-4bd3-9d21-5db803cd221b
-- title:
--   Gt BCPf: coord glue
-- statement:
--   The Gt BCPf construction uses the coord glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L139-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L139-L186

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
open GluingInclusion

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.coord_glue {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
    (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
    (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) (x : Multiplicative X),
      φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))
    (hgood : ∀ x ∈ W, ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, x ∈ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀),
      IsAffineOpen V₁ → Function.Bijective
        (AddMonoidAlgebra.liftNCRingHom (q.app V₁).hom (φ V₁ (h₁.trans hV₀))
          (fun _ _ => Commute.all _ _)))
    (V : B.Opens) (hV : IsAffineOpen V) (h : V ≤ W) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)) := by sorry
