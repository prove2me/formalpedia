-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P02_functorialInverse_tensor_bijective
-- name    : QAlgorithms.Papers.Independent.Gap48.P02.functorialInverse_tensor_bijective
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:49:58.168113+00:00
-- url     : https://prove2.me/theorems/7331a3c3-cbc4-4c40-b46f-399146e91588
-- title:
--   Lemma 53: tensoring by a morphism gives bijections
-- statement:
--   Let $M$ be a monoidal category admitting a covariant endofunctor $i$ and a natural isomorphism $x\otimes i(x)\cong\mathbf{1}$. For every morphism $f:x\to x'$ and all objects $y,z$, both maps below are bijections:
--
--   $$\begin{aligned}\operatorname{Hom}_M(y,z)&\longrightarrow\operatorname{Hom}_M(y\otimes x,z\otimes x'),&h&\longmapsto h\otimes f,\\\operatorname{Hom}_M(y,z)&\longrightarrow\operatorname{Hom}_M(x\otimes y,x'\otimes z),&h&\longmapsto f\otimes h.\end{aligned}$$
--
--   These are cancellation statements for tensoring by an arbitrary morphism, on either side. The printed letter $C$ in the source denotes the same category $M$.
-- source:
--   Central Extensions of Smooth 2-Groups and a Finite-Dimensional String 2-Group, arXiv:0911.2483v3, PDF p. 20, Lemma 53

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P02

namespace QAlgorithms.Papers.Independent.Gap48.P02

open CategoryTheory MonoidalCategory

universe v u

/-- Lemma 53, PDF p. 20: both tensor maps on the indicated hom sets
are bijective. The printed C in the source denotes M. -/
theorem functorialInverse_tensor_bijective
    (M : Type u) [Category.{v} M] [MonoidalCategory M]
    (h : Nonempty (FunctorialInverseChoice M))
    {x xTarget : M} (f : x ⟶ xTarget) (y z : M) :
    Function.Bijective (fun g : y ⟶ z => g ⊗ₘ f) ∧
      Function.Bijective (fun g : y ⟶ z => f ⊗ₘ g) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P02
