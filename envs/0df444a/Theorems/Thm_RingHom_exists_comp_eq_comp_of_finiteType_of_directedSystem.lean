-- Prove2me | Theorems.Thm_RingHom_exists_comp_eq_comp_of_finiteType_of_directedSystem
-- name    : RingHom.exists_comp_eq_comp_of_finiteType_of_directedSystem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/f50f6739-9454-5ffd-b529-7ded2541be91
-- title:
--   Maps from a finite-type ring into a directed colimit are eventually equal
-- statement:
--   Let $\iota$ be a non-empty preorder that is directed for $\le$, let $S_i$ be a commutative ring for each $i\in\iota$, and let $t_{ij}\colon S_i\to S_j$ be ring homomorphisms given for each pair $i\le j$, satisfying $t_{ii}=\mathrm{id}_{S_i}$ for every proof of $i\le i$ and $t_{jk}\circ t_{ij}=t_{ik}$ for all $i\le j\le k$. Let $L$ be a commutative ring equipped with ring homomorphisms $c_i\colon S_i\to L$ such that $c_j\circ t_{ij}=c_i$ whenever $i\le j$, such that every $x\in L$ is of the form $c_i(y)$ for some $i$ and some $y\in S_i$, and such that whenever $c_i(y)=c_i(z)$ for $y,z\in S_i$ there exist $j\ge i$ with $t_{ij}(y)=t_{ij}(z)$; that is, $L$ together with the $c_i$ realises the colimit of the system. Let $R$ be a commutative ring that is of finite type as a $\mathbb{Z}$-algebra, let $i\in\iota$ and let $\psi,\psi'\colon R\to S_i$ be ring homomorphisms with $c_i\circ\psi=c_i\circ\psi'$. The conclusion is that there exist $j$ and a proof of $i\le j$ with $t_{ij}\circ\psi=t_{ij}\circ\psi'$.
--
--   This is the injectivity half of the statement that a ring of finite type over $\mathbb{Z}$ is a compact object in commutative rings, i.e. that $\varinjlim \operatorname{Hom}(R,S_i)\to\operatorname{Hom}(R,\varinjlim S_i)$ is injective; it is one of the standard limit arguments of EGA IV §8. It is used in the Čerednik–Drinfeld part of the development, to descend equalities of isomorphisms of fake elliptic curves with full level structure along a directed colimit of base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_exists_comp_eq_comp_of_finiteType_of_directedSystem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.exists_comp_eq_comp_of_finiteType_of_directedSystem
    (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R]
    (i : ι) (ψ ψ' : R →+* S i) (h : (c i).comp ψ = (c i).comp ψ') :
    ∃ (j : ι) (hij : i ≤ j), (t i j hij).comp ψ = (t i j hij).comp ψ' := by sorry
