-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points
-- name    : PDivisibleGroup.exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/53f750a5-c499-5a4a-939b-3ebfef5dbb8c
-- title:
--   Splitting of the Tate module of a height-h+h' group
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime, and let $G$, $H$, $P$ be $p$-divisible groups over $R$ (in the project's sense: systems of finite free cocommutative commutative Hopf $R$-algebras $\mathcal{O}(G_v)$ with surjective bialgebra transition maps of the prescribed kernel and $\operatorname{rank}_R \mathcal{O}(G_v) = p^{vh}$) of heights $h$, $h'$ and $h + h'$ respectively. Suppose given $R$-bialgebra maps $i^G_v : \mathcal{O}(G_v) \to \mathcal{O}(P_v)$ and $i^H_v : \mathcal{O}(H_v) \to \mathcal{O}(P_v)$ for all $v$, compatible with the transitions in the sense that $i^G_v \circ \mathrm{tr}^G_v = \mathrm{tr}^P_v \circ i^G_{v+1}$ and likewise for $i^H$, and suppose that for every commutative $R$-algebra $L$ and every $v$ the map sending an $R$-algebra homomorphism $x : \mathcal{O}(P_v) \to L$ to the pair $(x \circ i^G_v,\; x \circ i^H_v)$ is a bijection $P_v(L) \to G_v(L) \times H_v(L)$, and that each of its two components is multiplicative for the convolution products on these point sets. Then for every $R$-algebra $L$ which is a field there is a $\mathbb{Z}_p$-linear isomorphism $TP$ from $T_p(P(L))$ onto $T_p(G(L)) \times T_p(H(L))$, where $T_p(M)$ denotes the group of sequences $(x_n)_{n \in \mathbb{N}}$ in $M$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, and $P(L)$ is the direct limit of the $P_v(L)$ written additively, with the following levelwise description: whenever the $n$-th entry of $x \in T_p(P(L))$ is the image of a level-$w$ point $g \in P_w(L)$, the $n$-th entries of the two components of $TP(x)$ are the images of the level-$w$ points $g \circ i^G_w$ and $g \circ i^H_w$.
--
--   This identifies the Tate module of a $p$-divisible group $P$ that represents the product of $G$ and $H$ on points with the product of their Tate modules, componentwise along the given inclusions; the hypotheses are exactly the properties a product of $p$-divisible groups is known to have, so the result can be applied without reference to the construction of the product. It is used in the passage from additive maps on points to families of bialgebra maps over rings of integers, and it rests on the functoriality of Tate modules given by [`PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq`](thm.html#PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points
    {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h')
    (P : PDivisibleGroup R p (h + h'))
    (iG : ∀ v : ℕ, G.level v →ₐc[R] P.level v) (iH : ∀ v : ℕ, H.level v →ₐc[R] P.level v)
    (hiG : ∀ v : ℕ, (iG v).comp (G.transition v) = (P.transition v).comp (iG (v + 1)))
    (hiH : ∀ v : ℕ, (iH v).comp (H.transition v) = (P.transition v).comp (iH (v + 1)))
    (hpts : ∀ (L : Type) [CommRing L] [Algebra R L] (v : ℕ),
          Function.Bijective (fun x : P.Point L v =>
            ((PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) :
                G.Point L v),
             (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) :
                H.Point L v))) ∧
          ∀ x y : P.Point L v,
            (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iG v : G.level v →ₐ[R] P.level v)) :
                G.Point L v) =
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) *
                PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iG v : G.level v →ₐ[R] P.level v)) ∧
            (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iH v : H.level v →ₐ[R] P.level v)) :
                H.Point L v) =
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) *
                PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iH v : H.level v →ₐ[R] P.level v))) :
    ∀ (L : Type) [Field L] [Algebra R L],
        ∃ TP : TateModule p (P.Points L) ≃ₗ[ℤ_[p]] TateModule p (G.Points L) × TateModule p (H.Points L),
          (∀ (x : TateModule p (P.Points L)) (n w : ℕ) (g : P.Point L w),
            P.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → P.Points L) n →
            (((TP x).1 : TateModule p (G.Points L)) : ℕ → G.Points L) n =
              G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
                ((PDivisibleGroup.Point.toAlgHom g).comp (iG w : G.level w →ₐ[R] P.level w)))) ∧
            (((TP x).2 : TateModule p (H.Points L)) : ℕ → H.Points L) n =
              H.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
                ((PDivisibleGroup.Point.toAlgHom g).comp (iH w : H.level w →ₐ[R] P.level w))))) := by sorry
