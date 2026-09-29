-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isElliptic_map_veluQuotient_j
-- name    : WeierstrassCurve.exists_isElliptic_map_veluQuotient_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/46ed9801-e98b-5b6a-b8ce-bdb3a778b83e
-- title:
--   Base change of a Vélu quotient and its j-invariant
-- statement:
--   Let $R$ and $R'$ be fields, let $W$ be a Weierstrass curve over $R$ with coefficients $a_1,\dots,a_6$, let $f : R \to R'$ be a ring homomorphism, and let $S$ be a finite set of pairs in $R \times R$ (thought of as affine points). Here the Vélu quotient `W.veluQuotient S` is the Weierstrass curve over $R$ with the same $a_1, a_2, a_3$ as $W$, with $a_4$ replaced by $a_4 - 5\sum_{P \in S} t(P)$ and $a_6$ replaced by $a_6 - b_2\sum_{P \in S} t(P) - 7\sum_{P \in S} w(P)$, where $t$ and $w$ are the quantities `W.veluT` and `W.veluW` evaluated at the two coordinates of $P$ and $b_2$ is the usual invariant of $W$. Assume that `W.veluQuotient S` is elliptic, i.e. its discriminant is a unit, so that its $j$-invariant is defined. The conclusion asserts the existence of a proof that the Vélu quotient of the base-changed curve `W.map f` by the image of $S$ under $(x,y) \mapsto (f(x), f(y))$ is again elliptic, together with the equality of its $j$-invariant with $f$ applied to the $j$-invariant of `W.veluQuotient S`. No hypothesis is imposed on $f$ beyond its being a homomorphism of fields, and no hypothesis relates $S$ to the points of $W$.
--
--   This is the compatibility of Vélu's explicit quotient formulas with extension of the base field, in the form needed to transport a $j$-invariant computed over one field to a larger one. It is used in the construction of the dictionary between roots of modular polynomials and cyclic subgroups, namely by [`ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two`](thm.html#ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two) and [`ModularCurve.exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ`](thm.html#ModularCurve.exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isElliptic_map_veluQuotient_j.lean

import Definitions.Def_WeierstrassCurve_VeluQuotientMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_isElliptic_map_veluQuotient_j {R R' : Type*} [Field R] [Field R']
    [DecidableEq R'] (W : WeierstrassCurve R) (f : R →+* R') (S : Finset (R × R))
    (hQ : (W.veluQuotient S).IsElliptic) :
    ∃ hQ' : ((W.map f).veluQuotient (S.image (Prod.map f f))).IsElliptic,
      @WeierstrassCurve.j R' _ ((W.map f).veluQuotient (S.image (Prod.map f f))) hQ' =
        f (@WeierstrassCurve.j R _ (W.veluQuotient S) hQ) := by sorry
