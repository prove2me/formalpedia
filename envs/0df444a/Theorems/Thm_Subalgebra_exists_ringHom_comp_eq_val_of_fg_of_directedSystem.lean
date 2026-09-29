-- Prove2me | Theorems.Thm_Subalgebra_exists_ringHom_comp_eq_val_of_fg_of_directedSystem
-- name    : Subalgebra.exists_ringHom_comp_eq_val_of_fg_of_directedSystem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/5d793ecc-f085-5626-8e57-29069174a0c5
-- title:
--   Lifting finitely generated ℤ-subalgebras along a directed colimit of rings
-- statement:
--   Let $\iota$ be a non-empty directed preorder, let $S_i$ be a commutative ring for each $i \in \iota$, and let $t_{ij} : S_i \to S_j$ be ring homomorphisms given for each $i \le j$, subject to $t_{ii} = \mathrm{id}_{S_i}$ for every reflexivity witness and to $t_{jk} \circ t_{ij} = t_{ik}$ for all $i \le j \le k$. Let $L$ be a commutative ring equipped with ring homomorphisms $c_i : S_i \to L$ satisfying $c_j \circ t_{ij} = c_i$ for all $i \le j$, such that every element of $L$ is of the form $c_i(y)$ for some index $i$ and some $y \in S_i$, and such that whenever $c_i(y) = c_i(z)$ for $y, z \in S_i$ there exist $j \ge i$ with $t_{ij}(y) = t_{ij}(z)$; thus the $c_i$ exhibit $L$ as the colimit of the system. Finally let $T \subseteq L$ be a $\mathbb{Z}$-subalgebra that is finitely generated. The conclusion is twofold: first, for every index $i_0$ there are an index $j \ge i_0$ and a ring homomorphism $\psi : T \to S_j$ with $c_j \circ \psi$ equal to the inclusion $T \hookrightarrow L$; second, if $\psi, \psi' : T \to S_i$ satisfy $c_i \circ \psi = c_i \circ \psi'$, then $t_{ij} \circ \psi = t_{ij} \circ \psi'$ for some $j \ge i$.
--
--   This is the ring-theoretic limit statement that $\operatorname{Hom}(T, \varinjlim_i S_i) = \varinjlim_i \operatorname{Hom}(T, S_i)$ for a finitely generated $\mathbb{Z}$-algebra $T$, in the cofinal form (lifts exist above any prescribed index) together with eventual uniqueness of lifts. It serves as the bridge between results stated in terms of a finitely generated $\mathbb{Z}$-subalgebra of a single ring and results about an abstract directed system, and is used in the descent of pullback squares and of isomorphisms of fake elliptic curves with full level structure to a finite stage of a directed colimit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_exists_ringHom_comp_eq_val_of_fg_of_directedSystem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subalgebra.exists_ringHom_comp_eq_val_of_fg_of_directedSystem
    (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (T : Subalgebra ℤ L) (hT : T.FG) :
    (∀ i₀ : ι, ∃ (j : ι) (_ : i₀ ≤ j) (ψ : ↥T →+* S j), (c j).comp ψ = T.val.toRingHom) ∧
    (∀ (i : ι) (ψ ψ' : ↥T →+* S i), (c i).comp ψ = (c i).comp ψ' →
        ∃ (j : ι) (h : i ≤ j), (t i j h).comp ψ = (t i j h).comp ψ') := by sorry
