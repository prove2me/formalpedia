-- Prove2me | Theorems.Thm_ValuationSubring_exists_window_and_adapted_basis
-- name    : ValuationSubring.exists_window_and_adapted_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/b522fe3b-ee5d-5f84-ad77-7d7fb8bcd97a
-- title:
--   Finite window and valuation-adapted basis for an independent family
-- statement:
--   Let $L$ be a field, $\iota$ an index set, and $O \subseteq L$ a Noetherian subring. Let $x : \mathrm{Fin}\,r \to \iota \to L$ be a finite family of $L$-valued functions on $\iota$ which is linearly independent in the strong coordinatewise sense that any $a : \mathrm{Fin}\,r \to L$ with $\sum_i a_i\,x_i(n) = 0$ for every $n \in \iota$ has all $a_i = 0$, and assume every coordinate $x_i(n)$ lies in $O$. Then there are a finite subset $W \subseteq \iota$ and an element $\delta \in O$, $\delta \neq 0$, with the following two properties. First (window property): for every subring $A$ of $L$ containing $O$ and every $a : \mathrm{Fin}\,r \to L$, if $\sum_i a_i\,x_i(n) \in A$ for all $n \in W$, then $\sum_i a_i\,x_i(n) \in A$ for all $n \in \iota$. Second: for every valuation subring $A$ of $L$ whose underlying subring contains $O$ there exist a family $t : \mathrm{Fin}\,r \to \iota \to L$ and matrices $M, M'$ of size $r \times r$ over $L$ such that $t_j(n) = \sum_i M_{ji}\,x_i(n)$ and $x_i(n) = \sum_j M'_{ij}\,t_j(n)$ for all $i$, $j$, $n$; all $\delta M_{ji}$ and all $M'_{ij}$ lie in $A$; the family $t$ is saturated along $A$, in that any $a : \mathrm{Fin}\,r \to L$ with $\sum_j a_j\,t_j(n) \in A$ for all $n$ has all $a_j \in A$; all coordinates $t_j(n)$ lie in $A$; and the induced functions $n \mapsto \overline{t_j(n)}$ with values in the residue field of $A$ form a linearly independent family over that residue field.
--
--   This is the linear-algebra input that makes a single finite set of indices and a single denominator $\delta$ serve uniformly for all valuation subrings of $L$ above $O$: the window $W$ replaces integrality at all indices by integrality at finitely many, and the basis $t$ is the echelon (orthonormal, residually independent) basis adapted to a given valuation subring, with transition matrices bounded by $\delta$. It is used by [`ModularCurve.exists_uniform_adapted_basis`](thm.html#ModularCurve.exists_uniform_adapted_basis), where $x$ records the coefficient sequences of $q$-expansions and $O$ is a ring of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_window_and_adapted_basis.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_window_and_adapted_basis
    {L : Type*} [Field L] {ι : Type*} (O : Subring L) [IsNoetherianRing O] {r : ℕ}
    (x : Fin r → ι → L)
    (hx : ∀ a : Fin r → L, (∀ n, ∑ i, a i * x i n = 0) → ∀ i, a i = 0)
    (hO : ∀ i n, x i n ∈ O) :
    ∃ (W : Finset ι) (δ : L), δ ∈ O ∧ δ ≠ 0 ∧
      (∀ A : Subring L, O ≤ A → ∀ a : Fin r → L,
          (∀ n ∈ W, ∑ i, a i * x i n ∈ A) → ∀ n, ∑ i, a i * x i n ∈ A) ∧
      ∀ A : ValuationSubring L, O ≤ A.toSubring →
        ∃ (t : Fin r → ι → L) (M M' : Matrix (Fin r) (Fin r) L),
          (∀ j n, t j n = ∑ i, M j i * x i n) ∧ (∀ i n, x i n = ∑ j, M' i j * t j n) ∧
          (∀ j i, δ * M j i ∈ A) ∧ (∀ i j, M' i j ∈ A) ∧
          (∀ a : Fin r → L, (∀ n, ∑ j, a j * t j n ∈ A) → ∀ j, a j ∈ A) ∧
          ∃ ht : ∀ j n, t j n ∈ A,
            LinearIndependent (IsLocalRing.ResidueField A)
              (fun j => fun n : ι => IsLocalRing.residue A ⟨t j n, ht j n⟩) := by sorry
