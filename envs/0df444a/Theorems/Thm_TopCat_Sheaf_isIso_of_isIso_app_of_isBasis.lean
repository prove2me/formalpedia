-- Prove2me | Theorems.Thm_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis
-- name    : TopCat.Sheaf.isIso_of_isIso_app_of_isBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/8dd3210c-d7ef-5b70-b410-806840131e56
-- title:
--   Sheaf morphism is an isomorphism if it is on a basis
-- statement:
--   Let $C$ be a category, $X$ a topological space (an object of `TopCat`), and let $B : \iota \to$ `Opens X` be a family of open subsets of $X$ indexed by a type $\iota$ whose range `Set.range B` is a basis of the topology of $X$, in the sense of `Opens.IsBasis`. Let $F$ and $G$ be $C$-valued sheaves on $X$, i.e. objects of `TopCat.Sheaf C X`, and let $\varphi : F \to G$ be a morphism of sheaves, that is, a natural transformation $\varphi.1$ between the underlying presheaves. Assume that for every index $i$ the component $\varphi.1$ at the object `op (B i)` of the opposite of the lattice of opens, namely the map $F(B_i) \to G(B_i)$, is an isomorphism in $C$. The conclusion is that $\varphi$ is an isomorphism in the category `TopCat.Sheaf C X`. No completeness, limit-existence or concreteness hypothesis is imposed on $C$; the basis is given as the range of an indexed family, and the isomorphism hypothesis is indexed by $\iota$ rather than by members of the basis.
--
--   This is the standard statement that a $C$-valued sheaf on a topological space is determined by its values on a basis of opens, in the form of a recognition criterion for isomorphisms of sheaves. It is used in the theory of sheaves of modules on schemes, for instance to recognise when a sheaf of modules on an affine scheme is the sheaf associated with its global sections by testing the basic opens $D(f)$, and to check that a pullback comparison map is an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w u'

open CategoryTheory Opposite TopologicalSpace

theorem TopCat.Sheaf.isIso_of_isIso_app_of_isBasis {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G : TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ := by sorry
