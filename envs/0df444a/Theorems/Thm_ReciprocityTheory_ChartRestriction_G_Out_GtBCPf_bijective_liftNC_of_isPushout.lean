-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_bijective_liftNC_of_isPushout
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.bijective_liftNC_of_isPushout
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:54.248191+00:00
-- url     : https://prove2.me/theorems/3c8d3d76-eee0-507c-ab81-69538ad0618b
-- title:
--   Gt BCPf: bijective lift NC of is Pushout
-- statement:
--   The Gt BCPf construction uses the bijective lift NC of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L53-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L53-L123

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
variable {R A R' A' : CommRingCat.{u}} {qa : R ⟶ A} {ba : R ⟶ R'} {ga : A ⟶ A'} {qa' : R' ⟶ A'}
  {X : Type u} [AddCommMonoid X]

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.bijective_liftNC_of_isPushout (hP : IsPushout qa ba ga qa')
    (φ : Multiplicative X →* A) (φ' : Multiplicative X →* A') (hφ' : ∀ x, φ' x = ga (φ x))
    (hφ : Function.Bijective (AddMonoidAlgebra.liftNCRingHom qa.hom φ (fun _ _ => Commute.all _ _))) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom qa'.hom φ' (fun _ _ => Commute.all _ _)) := by sorry
