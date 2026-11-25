-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_GluingInclusion_surj_of_cover
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.surj_of_cover
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:06.331707+00:00
-- url     : https://prove2.me/theorems/9f8a67c6-d289-4943-b6b2-ed671679ec2e
-- title:
--   Gluing Inclusion: surj of cover
-- statement:
--   The Gluing Inclusion construction uses the surj of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L77-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/SurjOfCover.lean#L77-L133

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

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.GluingInclusion.surj_of_cover {V : B.Opens} (h : V ≤ W) {ι : Type} [Finite ι] (U : ι → B.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ iSup U)
    (hsurj : ∀ i, Function.Surjective (cm q φ (U i) ((hU i).trans h)))
    (hinj2 : ∀ i j, Function.Injective (cm q φ (U i ⊓ U j) (inf_le_left.trans ((hU i).trans h)))) :
    Function.Surjective (cm q φ V h) := by sorry
