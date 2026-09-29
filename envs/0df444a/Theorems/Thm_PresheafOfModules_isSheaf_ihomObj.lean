-- Prove2me | Theorems.Thm_PresheafOfModules_isSheaf_ihomObj
-- name    : PresheafOfModules.isSheaf_ihomObj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/f5f85dde-728b-5d58-9cda-f64b3b1408a5
-- title:
--   Internal Hom of presheaves of modules is a sheaf
-- statement:
--   Let $C$ be a category whose objects and morphisms lie in a single universe, let $R : C^{\mathrm{op}} \to \mathbf{CommRing}$ be a presheaf of commutative rings on $C$, and let $F$ and $N$ be presheaves of modules over the associated presheaf of rings $R$ followed by the forgetful functor to $\mathbf{Ring}$. Let $J$ be a Grothendieck topology on $C$ and assume that the underlying presheaf of abelian groups of $N$ is a $J$-sheaf. The assertion is that the underlying presheaf of abelian groups of [`PresheafOfModules.ihomObj F N`](def/PresheafOfModules_InternalHom.html#L139) is then a $J$-sheaf as well. Here `ihomObj F N` is the presheaf of modules whose value at $X \in C^{\mathrm{op}}$ is the additive group `naturalFamilies F N X` of families $\varphi$ assigning to every $f : X \to Y$ an $R(Y)$-linear map $\varphi(f) : F(Y) \to N(Y)$, subject to the predicate `IsNatural`, which says that $N(g)(\varphi(f)(x)) = \varphi(f \circ g)(F(g)(x))$ for all $g : Y \to Z$ and $x \in F(Y)$; restriction along $h : X \to X'$ sends $\varphi$ to $f \mapsto \varphi(h \circ f)$, and $(r \cdot \varphi)(f)(x) = R(f)(r) \cdot \varphi(f)(x)$. No sheaf hypothesis is imposed on $F$ or on $R$.
--
--   This is the standard statement that the internal Hom (Hom sheaf) $\mathcal{H}om_R(F,N)$ of presheaves of modules on a site is a sheaf as soon as the target is, with no condition on the source or on the ring object. Within the development it provides the sheaf property needed to form duals of modules on schemes and the monoidal structure on the relevant categories of sheaves of modules; it is used by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.dual`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.dual), [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse) and [`PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`](thm.html#PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PresheafOfModules_isSheaf_ihomObj.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

theorem PresheafOfModules.isSheaf_ihomObj {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {J : GrothendieckTopology C} (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (PresheafOfModules.ihomObj F N).presheaf := by sorry
