-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
-- name    : PDivisibleGroup.CartierDuality.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/de1f18a3-6778-5b17-9375-af6ee42aac30
-- title:
--   Double annihilators and Tate-module lifting for Cartier-dual pairings
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime, $h$ a natural number, and let $G$, $G'$ be $p$-divisible groups over $R$ of height datum $(p,h)$, i.e. systems of finite free cocommutative Hopf $R$-algebras $G.\mathrm{level}\,v$ of rank $p^{vh}$ with surjective transition maps whose kernels are the $p^v$-torsion ideals. Let $D$ be a Cartier duality between them, consisting of isomorphisms $G'.\mathrm{level}\,v \cong \mathrm{CartierDual}\,R\,(G.\mathrm{level}\,v)$ compatible with the transition maps and multiplication by $p$, and write $\mathrm{pair}\,K\,w$ for the induced pairing on points, the sum $\sum_i f(b_i)\,\psi(\,(D.\mathrm{toDualEquiv}\,w)^{-1}(b^i))$ over a chosen basis $b$ of $G.\mathrm{level}\,w$; here $G.\mathrm{Point}\,K\,w$ is the set of $R$-algebra maps $G.\mathrm{level}\,w \to K$ with the convolution group law. Let $K$ be an algebraically closed field of characteristic zero which is an $R$-algebra. Two assertions are made. First, for every $w$, every subgroup $H \le G.\mathrm{Point}\,K\,w$ and every point $z$: if $\mathrm{pair}\,K\,w\,z\,\psi = 1$ for all $\psi \in G'.\mathrm{Point}\,K\,w$ annihilating $H$, then $z \in H$. Second, given subgroups $H(w) \le G.\mathrm{Point}\,K\,w$ such that $G.\mathrm{pointIncl}\,K\,w\,z \in H(w+1)$ implies $z \in H(w)$, and given $\psi_1 \in G'.\mathrm{Point}\,K\,1$ with $\mathrm{pair}\,K\,1\,z\,\psi_1 = 1$ for all $z \in H(1)$, there is an element $y$ of $\mathrm{TateModule}\,p\,(G'.\mathrm{Points}\,K)$ — a sequence $y : \mathbb{N} \to G'.\mathrm{Points}\,K$ in the direct limit of the $G'.\mathrm{Point}\,K\,w$ (written additively) satisfying $p^n y_n = 0$ and $p\,y_{n+1} = y_n$ — with $y_1$ the image of $\psi_1$ under $G'.\mathrm{pointsMkAdd}\,K\,1$, such that for every $w$ and every $\psi \in G'.\mathrm{Point}\,K\,w$ whose image in the direct limit is $y_w$ one has $\mathrm{pair}\,K\,w\,z\,\psi = 1$ for all $z \in H(w)$.
--
--   These are the two group-theoretic consequences of perfectness of the Cartier pairing on geometric points in characteristic zero: the double-annihilator property at each level $w$, and the surjectivity, in the form of a coherent sequence in the Tate module, of the maps between successive annihilators of a descending-compatible family of subgroups. The statement is used in [`PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff`](thm.html#PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff), and its proof cites the perfectness and character-realisation statement [`PDivisibleGroup.CartierDuality.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed`](thm.html#PDivisibleGroup.CartierDuality.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed), the basis-independence and transpose properties of the Cartier pairing, and the count of $K$-points of a finite free Hopf algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] :
    (∀ (w : ℕ) (H : Subgroup (G.Point K w)) (z : G.Point K w),
      (∀ ψ : G'.Point K w, (∀ z' ∈ H, D.pair K w z' ψ = 1) → D.pair K w z ψ = 1) → z ∈ H) ∧
    (∀ (H : ∀ w : ℕ, Subgroup (G.Point K w)),
      (∀ (w : ℕ) (z : G.Point K w), G.pointIncl K w z ∈ H (w + 1) → z ∈ H w) →
      ∀ ψ₁ : G'.Point K 1, (∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) →
        ∃ y : TateModule p (G'.Points K),
          (y : ℕ → G'.Points K) 1 = G'.pointsMkAdd K 1 (Additive.ofMul ψ₁) ∧
          ∀ (w : ℕ) (ψ : G'.Point K w),
            G'.pointsMkAdd K w (Additive.ofMul ψ) = (y : ℕ → G'.Points K) w →
            ∀ z ∈ H w, D.pair K w z ψ = 1) := by sorry
