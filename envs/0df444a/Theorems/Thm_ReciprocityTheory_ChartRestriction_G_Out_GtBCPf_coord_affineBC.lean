-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_coord_affineBC
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.coord_affineBC
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:14.769522+00:00
-- url     : https://prove2.me/theorems/15c0447c-69a9-4cae-b805-94b4e9dff3e4
-- title:
--   Gt BCPf: coord affine BC
-- statement:
--   The Gt BCPf construction uses the coord affine BC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L127-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L127-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
universe u

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.coord_affineBC {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B}
    {b : B' ⟶ B}
    (sq : IsPullback g q' q b) (hq : IsAffineHom q) {X : Type u} [AddCommMonoid X]
    {V : B.Opens} (hV : IsAffineOpen V) {V' : B'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V))
    (φ : Multiplicative X →* Γ(G, q ⁻¹ᵁ V)) (φ' : Multiplicative X →* Γ(G', q' ⁻¹ᵁ V'))
    (hφ' : ∀ x, φ' x = g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG (φ x))
    (hφ : Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.app V).hom φ (fun _ _ => Commute.all _ _))) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q'.app V').hom φ' (fun _ _ => Commute.all _ _)) := by sorry
