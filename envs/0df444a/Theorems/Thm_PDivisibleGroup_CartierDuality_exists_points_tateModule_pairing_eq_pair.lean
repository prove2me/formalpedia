-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair
-- name    : PDivisibleGroup.CartierDuality.exists_points_tateModule_pairing_eq_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/520169f0-8248-52e7-a6d7-1cb0efa09911
-- title:
--   Tate's map α from points to dual Tate module characters
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime, $h$ a natural number, and let $G,G'$ be $p$-divisible groups of height $h$ over $R$ in the sense of the project's structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): families of commutative cocommutative Hopf $R$-algebras `level v`, finite and free of $R$-rank $p^{vh}$, with surjective coalgebra-algebra transition maps whose kernels are the $p^v$-torsion ideals. Let $D$ be a Cartier duality datum between $G$ and $G'$, that is, coalgebra-algebra isomorphisms $G'.\mathrm{level}\,v \cong \mathrm{CartierDual}\,R\,(G.\mathrm{level}\,v)$ compatible with the transitions of $G'$ and multiplication by $p$ on $G$, and let $L$ be a commutative $R$-algebra. Then there exists an additive homomorphism $\alpha$ from $G.\mathrm{Points}\,L$, the direct limit over $v$ of the groups $G.\mathrm{Point}\,L\,v$ of $R$-algebra maps $G.\mathrm{level}\,v \to L$ under convolution, to the $\mathbb{Z}_p$-linear maps from $\mathrm{TateModule}\,p\,(G'.\mathrm{Points}\,L)$ — the sequences $(y_n)$ in $G'.\mathrm{Points}\,L$ with $p^n y_n = 0$ and $p\,y_{n+1} = y_n$ — to the $p$-primary component of $\mathrm{Additive}\,L^\times$, such that: (1) for every level $v$, every $f \in G.\mathrm{Point}\,L\,v$, every $y$ in the Tate module and every $\psi \in G'.\mathrm{Point}\,L\,v$ whose image in $G'.\mathrm{Points}\,L$ is the component $y_v$, the unit $\alpha([f])(y)$, viewed in $L$, equals the Cartier pairing $D.\mathrm{pair}\,L\,v\,f\,\psi = \sum_i f(b_i)\,\psi\bigl((D.\mathrm{toDualEquiv}\,v)^{-1}(b.\mathrm{coord}\,i)\bigr)$ for the chosen $R$-basis $b$ of $G.\mathrm{level}\,v$; and (2) for every $R$-algebra automorphism $\sigma$ of $L$, every $z \in G.\mathrm{Points}\,L$ and every $y$ in the Tate module, the element of $L$ underlying $\alpha(\sigma \cdot z)(\sigma y)$, with $\sigma$ acting on the Tate module componentwise through `tateModuleRep`, equals $\sigma$ applied to the element of $L$ underlying $\alpha(z)(y)$.
--
--   This is the existence-and-characterisation half of the construction of the map denoted $\alpha_0$ in Tate's theory of $p$-divisible groups: Cartier duality turns the $p$-adic Tate module of the dual group into characters of the points of $G$ with values in the $p$-power roots of unity of $L$, compatibly with the Galois action. It is used in the proof of [`PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff`](thm.html#PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_PrimaryTorsion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.exists_points_tateModule_pairing_eq_pair
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (L : Type) [CommRing L] [Algebra R L] :
    ∃ α : G.Points L →+ (TateModule p (G'.Points L) →ₗ[ℤ_[p]] PrimaryTorsion p (Additive Lˣ)),
      (∀ (v : ℕ) (f : G.Point L v) (y : TateModule p (G'.Points L)) (ψ : G'.Point L v),
          G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v →
          ((Additive.toMul ((α (G.pointsMkAdd L v (Additive.ofMul f)) y :
              PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) = D.pair L v f ψ) ∧
      (∀ (σ : L ≃ₐ[R] L) (z : G.Points L) (y : TateModule p (G'.Points L)),
          ((Additive.toMul ((α (σ • z) (G'.tateModuleRep L σ y) :
              PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) =
            σ (((Additive.toMul ((α z y : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L))) := by sorry
