-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_finrank_cotangent_one_add_finrank_cotangent_one_eq_height
-- name    : PDivisibleGroup.CartierDuality.finrank_cotangent_one_add_finrank_cotangent_one_eq_height
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/efada4dd-f81e-57f8-a312-2c6c2ce404ca
-- title:
--   Tate's relation dim G+dim G'=h under Cartier duality
-- statement:
--   Let $k$ be a field of characteristic $p$, with $p$ prime, let $h$ be a natural number, and let $G$ and $G'$ be $p$-divisible groups over $k$ of height $h$ in the sense of the project's structure: each consists of a family of commutative rings $G.\mathrm{level}\,v$ carrying Hopf algebra structures over $k$ that are cocommutative, finite and free as $k$-modules, together with surjective bialgebra maps $\mathrm{transition}_v\colon G.\mathrm{level}\,(v+1)\to G.\mathrm{level}\,v$, subject to $\operatorname{finrank}_k(G.\mathrm{level}\,v)=p^{vh}$ and to the requirement that the kernel of $\mathrm{transition}_v$ be the image of the augmentation ideal (the kernel of the counit) under the algebra endomorphism $\mathrm{nsmulAlgHom}$ given by the $p^v$-th convolution power of the identity. Assume given a Cartier duality datum $D$ between $G$ and $G'$, that is, bialgebra isomorphisms $G'.\mathrm{level}\,v\simeq \operatorname{CartierDual}_k(G.\mathrm{level}\,v)=\operatorname{Hom}_k(G.\mathrm{level}\,v,k)$ for every $v$, satisfying the compatibility $\big(D.\mathrm{equiv}_v(\mathrm{transition}_v x)\big)(\mathrm{transition}_v a)=\big(D.\mathrm{equiv}_{v+1}x\big)(\mathrm{nsmulAlgHom}\,p\,(a))$ for all $x\in G'.\mathrm{level}\,(v+1)$ and $a\in G.\mathrm{level}\,(v+1)$. Then the $k$-dimensions of the cotangent spaces $I/I^2$ at level $1$, where $I$ denotes the respective augmentation ideal of $G.\mathrm{level}\,1$ and of $G'.\mathrm{level}\,1$, add up to $h$.
--
--   This is Tate's Proposition 3 for $p$-divisible groups over a base field of characteristic $p$: the dimensions of a $p$-divisible group and of its Cartier dual sum to the height. It feeds the project's account of the dimension of a $p$-divisible group, being cited by [`PDivisibleGroup.add_eq_height_of_hasDimension_of_cartierDuality`](thm.html#PDivisibleGroup.add_eq_height_of_hasDimension_of_cartierDuality) and by [`PDivisibleGroup.finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one`](thm.html#PDivisibleGroup.finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_finrank_cotangent_one_add_finrank_cotangent_one_eq_height.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.finrank_cotangent_one_add_finrank_cotangent_one_eq_height
    {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {h : ℕ}
    {G G' : PDivisibleGroup k p h} (D : G.CartierDuality G') :
    Module.finrank k (G.Cotangent 1) + Module.finrank k (G'.Cotangent 1) = h := by sorry
