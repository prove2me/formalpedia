-- Prove2me | Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
-- name    : PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/6cc34635-b2a9-5b15-b638-da1af9dddfbf
-- title:
--   Sheafification-local morphisms of presheaves of modules form a monoidal class
-- statement:
--   Let $C$ be a category and $J$ a Grothendieck topology on $C$, let $\mathcal{O} : C^{\mathrm{op}} \to \mathbf{CommRing}$ be a presheaf of commutative rings, let $R$ be a $J$-sheaf of rings, and let $\alpha$ be a morphism of presheaves of rings from the underlying presheaf of rings of $\mathcal{O}$ (that is, $\mathcal{O}$ followed by the forgetful functor $\mathbf{CommRing} \to \mathbf{Ring}$) to the underlying presheaf of $R$, assumed $J$-locally injective and $J$-locally surjective. Assume further that on presheaves of abelian groups the class $J.W$ of morphisms inverted by sheafification coincides with the locally bijective morphisms, and that presheaves of abelian groups on $(C,J)$ admit a weak sheafification. Consider the class of morphisms of presheaves of modules over the underlying presheaf of rings of $\mathcal{O}$ whose underlying morphism of presheaves of abelian groups, obtained by applying `PresheafOfModules.toPresheaf`, belongs to $J.W$. The assertion is that this class is monoidal in the sense of `MorphismProperty.IsMonoidal` for the sectionwise tensor product of presheaves of modules: besides being multiplicative, it is stable under whiskering on the right by an arbitrary presheaf of modules and under whiskering on the left.
--
--   This is the compatibility of sheafification with the tensor product of presheaves of modules, in the form of the hypothesis needed to equip the localisation of presheaves of modules at the locally bijective morphisms — that is, sheaves of modules — with a monoidal structure. It is used in the construction of tensor products of sheaves of modules, for instance for invertible ideal sheaves on a scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

theorem PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
    (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))).IsMonoidal := by sorry
