-- Prove2me | Theorems.Thm_PDivisibleGroup_cotangentBaseChange_bijective
-- name    : PDivisibleGroup.cotangentBaseChange_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/f600cbd7-ec3b-5dbe-bb05-6a379aadeda9
-- title:
--   Base change of the cotangent space of a p-divisible group
-- statement:
--   Let $R$ be a commutative ring, let $p$ and $h$ be natural numbers, and let $G$ be a $p$-divisible group over $R$ of height $h$ in the sense of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): a family of commutative rings $G.level\ v$ ($v \in \mathbb{N}$), each a cocommutative Hopf algebra over $R$ that is finite and free as an $R$-module of rank $p^{vh}$, together with surjective coalgebra–algebra maps $G.transition\ v : G.level(v+1) \to G.level\ v$ whose kernels are the ideals $(\ker \varepsilon).\mathrm{map}(\text{multiplication-by-}p^v)$ of $G.level(v+1)$. Let $S$ be a nontrivial commutative $R$-algebra and $v$ a natural number. Write $I_v = \ker(\varepsilon : G.level\ v \to R)$ for the augmentation ideal, $G.Cotangent\ v = I_v/I_v^2$, and $J = \ker(\varepsilon : S \otimes_R G.level\ v \to S)$ for the augmentation ideal of the base-changed bialgebra, with cotangent module $J/J^2$. The assertion is that the $S$-linear map `G.cotangentBaseChange S v` from $S \otimes_R (I_v/I_v^2)$ to $J/J^2$, obtained by base change from the map on cotangent modules induced by $x \mapsto 1 \otimes x$ (which carries $I_v$ into $J$), is bijective.
--
--   This is the statement that formation of the cotangent space along the unit section of a $p$-divisible group commutes with arbitrary base change, the Hopf-algebraic form of the base-change property of the conormal module of the unit section. It is used in the treatment of the dimension of a $p$-divisible group, being cited by [`PDivisibleGroup.exists_hasDimension`](thm.html#PDivisibleGroup.exists_hasDimension), [`PDivisibleGroup.free_cotangent_of_isArtinianRing_of_pow_eq_zero`](thm.html#PDivisibleGroup.free_cotangent_of_isArtinianRing_of_pow_eq_zero) and [`PDivisibleGroup.add_eq_height_of_hasDimension_of_cartierDuality`](thm.html#PDivisibleGroup.add_eq_height_of_hasDimension_of_cartierDuality).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_cotangentBaseChange_bijective.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.cotangentBaseChange_bijective
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] [Nontrivial S] (v : ℕ) :
    Function.Bijective (G.cotangentBaseChange S v) := by sorry
