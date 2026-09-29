-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed
-- name    : PDivisibleGroup.exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/cdad3158-4b17-515c-915e-931acef4540f
-- title:
--   Geometric points of a p-divisible group under field extension
-- statement:
--   Let $R$ be a commutative ring, let $p,h$ be natural numbers and let $G$ be a $p$-divisible group over $R$ of height data $(p,h)$ in the sense of the project's structure: a family of commutative $R$-Hopf algebras $G.\mathrm{level}\,v$ that are cocommutative and finite free as $R$-modules, with $\operatorname{rank}_R(G.\mathrm{level}\,v)=p^{vh}$, together with surjective coalgebra–algebra transition maps $G.\mathrm{level}(v+1)\to G.\mathrm{level}\,v$ whose kernel is the $p^v$-torsion ideal $(\mathrm{augIdeal})^{\,}$ image under multiplication by $p^v$. Let $L$ be an algebraically closed field and $L'$ a field, both $R$-algebras, and let $j : L \to L'$ be an $R$-algebra homomorphism. The assertion is the existence of a family of multiplicative isomorphisms $e_v : G.\mathrm{Point}\,L\,v \to G.\mathrm{Point}\,L'\,v$ between the convolution groups of $R$-algebra maps $G.\mathrm{level}\,v \to L$, respectively $\to L'$, and of an additive isomorphism $E$ between the direct limits $G.\mathrm{Points}\,L$ and $G.\mathrm{Points}\,L'$ of these groups along the level inclusions, such that: $e_v$ is given by post-composition with $j$, i.e. $e_v(x) = G.\mathrm{pointMap}\,j\,v\,x$; $E$ is the induced map $G.\mathrm{pointsMap}\,j$ on direct limits; $E$ commutes with the canonical maps $G.\mathrm{pointsMkAdd}$ from level $v$ into the limit, via $e_v$; and for all $R$-algebra automorphisms $\sigma$ of $L$ and $\sigma'$ of $L'$ with $j\circ\sigma = \sigma'\circ j$, one has $E(\sigma\cdot z)=\sigma'\cdot E(z)$ for all $z$. In effect the content is that post-composition with $j$ is bijective on points at each level and in the limit.
--
--   This is the statement that the geometric points of a $p$-divisible group are insensitive to enlarging an algebraically closed base field: every $L'$-point already comes from an $L$-point, compatibly with the Galois actions. It is used in the uniqueness-and-existence result reconstructing a family of bialgebra maps from an additive map on points over a discrete valuation ring lying over a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [Algebra R L] (L' : Type) [Field L'] [Algebra R L'] (j : L →ₐ[R] L') :
    ∃ (e : ∀ v : ℕ, G.Point L v ≃* G.Point L' v) (E : G.Points L ≃+ G.Points L'),
      (∀ (v : ℕ) (x : G.Point L v), e v x = G.pointMap j v x) ∧
      (∀ z : G.Points L, E z = G.pointsMap j z) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        E (G.pointsMkAdd L v (Additive.ofMul x)) = G.pointsMkAdd L' v (Additive.ofMul (e v x))) ∧
      (∀ (σ : L ≃ₐ[R] L) (σ' : L' ≃ₐ[R] L'), (∀ a : L, j (σ a) = σ' (j a)) →
        ∀ z : G.Points L, E (σ • z) = σ' • E z) := by sorry
