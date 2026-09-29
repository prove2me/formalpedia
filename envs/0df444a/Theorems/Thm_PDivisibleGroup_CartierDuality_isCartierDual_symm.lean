-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_isCartierDual_symm
-- name    : PDivisibleGroup.CartierDuality.isCartierDual_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/79ae210f-cfbd-50ba-9515-265a241ceed6
-- title:
--   Cartier duality of p-divisible groups is symmetric
-- statement:
--   Let $R$ be a commutative ring and let $p,h$ be natural numbers. A $p$-divisible group $G$ over $R$ of height $h$ in the sense used here is a family of types $G.\mathrm{level}\,v$ ($v\in\mathbb{N}$), each a commutative ring and a cocommutative Hopf algebra over $R$ that is finite and free as an $R$-module of rank $p^{vh}$, together with surjective bialgebra maps $G.\mathrm{transition}\,v\colon G.\mathrm{level}(v+1)\to G.\mathrm{level}\,v$ whose kernels are the ideals [`PDivisibleGroup.Hopf.torsionIdeal R (G.level (v+1)) (p^v)`](def/PDivisibleGroup_Basic.html#L157), that is, the images of the augmentation ideal under the $p^v$-th convolution power `nsmulAlgHom` of the identity. Given two such $G,G'$ and a term $D$ of the structure `G.CartierDuality G'`, consisting of bialgebra isomorphisms $e_v\colon G'.\mathrm{level}\,v \xrightarrow{\ \sim\ } \mathrm{CartierDual}\,R\,(G.\mathrm{level}\,v) = \mathrm{Hom}_R(G.\mathrm{level}\,v,R)$ satisfying, for all $v$, all $x\in G'.\mathrm{level}(v+1)$ and all $a\in G.\mathrm{level}(v+1)$, the identity $e_v(G'.\mathrm{transition}\,v\,x)(G.\mathrm{transition}\,v\,a) = e_{v+1}(x)\bigl(\mathrm{nsmulAlgHom}\,R\,(G.\mathrm{level}(v+1))\,p\,(a)\bigr)$, the conclusion is `G'.IsCartierDual G`: the type `CartierDuality G' G` is nonempty, i.e. there exists a family of bialgebra isomorphisms $G.\mathrm{level}\,v \cong \mathrm{Hom}_R(G'.\mathrm{level}\,v,R)$ satisfying the same compatibility with the roles of $G$ and $G'$ interchanged.
--
--   This is the symmetry (biduality) statement for the project's notion of Cartier duality of $p$-divisible groups: being a Cartier dual is a symmetric relation, the inverse duality being obtained from the evaluation isomorphism of a finite free Hopf algebra with its double dual. It is used in the study of the Tate module of a $p$-divisible group over a ring of integers, notably in [`PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers`](thm.html#PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers) and [`PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers`](thm.html#PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_isCartierDual_symm.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.isCartierDual_symm
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') :
    G'.IsCartierDual G := by sorry
