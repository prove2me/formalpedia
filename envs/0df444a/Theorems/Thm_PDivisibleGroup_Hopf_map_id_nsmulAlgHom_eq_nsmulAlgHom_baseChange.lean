-- Prove2me | Theorems.Thm_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
-- name    : PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/42fabd38-3a61-535b-923c-f31daf3523a8
-- title:
--   Multiplication by n on a bialgebra commutes with base change
-- statement:
--   Let $R$ be a commutative ring, $S$ a commutative $R$-algebra, and $A$ a commutative ring equipped with an $R$-bialgebra structure; let $n$ be a natural number. For a commutative $R$-bialgebra $A$ the project writes [`PDivisibleGroup.Hopf.nsmulAlgHom R A n`](def/PDivisibleGroup_Basic.html#L16) for the $R$-algebra endomorphism of $A$ obtained as the $n$-th power of the identity map $A \to A$ in the convolution monoid of $R$-algebra endomorphisms of $A$ (the monoid structure on $\mathrm{End}_{R\text{-alg}}(A)$ whose multiplication is $\varphi * \psi = (\varphi \otimes \psi) \circ \Delta$ followed by multiplication, with unit $\eta \circ \varepsilon$); on the spectrum this is the comorphism of multiplication by $n$ on the affine monoid scheme $\operatorname{Spec} A$. The assertion is an equality of $S$-algebra endomorphisms of $S \otimes_R A$, the latter carrying its base-changed $S$-bialgebra structure: the tensor product $\mathrm{id}_S \otimes \mathrm{nsmulAlgHom}_{R,A,n}$, formed via `Algebra.TensorProduct.map` from the identity of $S$ and the $n$-fold convolution power of $\mathrm{id}_A$, coincides with [`PDivisibleGroup.Hopf.nsmulAlgHom S (S ⊗[R] A) n`](def/PDivisibleGroup_Basic.html#L16), the $n$-fold convolution power of the identity of $S \otimes_R A$ over $S$.
--
--   This is the compatibility of multiplication by $n$ on a commutative affine monoid scheme with base change, in bialgebra form; it is used throughout the treatment of $p$-divisible groups, where the level-$v$ torsion ideals are defined by these endomorphisms, to compare an endomorphism of a finite flat group scheme or an isogeny of $p$-divisible groups with multiplication by a power of $p$ after reduction. It is cited in the construction of $p$-divisible towers with prescribed kernels, in the Cartier-duality estimates, and in the production of formally étale towers with bijective base change modulo $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

theorem PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (A : Type w) [CommRing A] [Bialgebra R A] (n : ℕ) :
    Algebra.TensorProduct.map (AlgHom.id S S) (PDivisibleGroup.Hopf.nsmulAlgHom R A n) =
      PDivisibleGroup.Hopf.nsmulAlgHom S (S ⊗[R] A) n := by sorry
