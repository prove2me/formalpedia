-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_nonSeparable_ear_decomposition
-- name    : WhitneyMatroid.Components.nonSeparable_ear_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:29:19.793884+00:00
-- url     : https://prove2.me/theorems/cac24bbd-f77b-4df3-b44a-d2c34a48ca17
-- title:
--   Theorem 17 — building a non-separable matroid from a circuit by adding circuits
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$, and let $X\subseteq E$ be non-separable with nullity $n(X)=n>0$. Then there are sets $N_1\subseteq N_2\subseteq\cdots\subseteq N_n$ with
--
--   1. $N_1$ a circuit of $M$ and $N_n = X$;
--   2. for $1\le i\le n$, $N_i$ is non-separable of nullity $n(N_i)=i$;
--   3. for $1\le i<n$, there is a circuit $P$ of $M$ with
--   $$
--   P\subseteq N_{i+1},\qquad N_{i+1}\setminus N_i\subseteq P,\qquad P\cap N_i\neq\emptyset ,
--   $$
--   i.e. $N_{i+1}$ arises from $N_i$ by adding a set of elements which forms a circuit with one or more elements of $N_i$.
--
--   This is Whitney's description of how any non-separable matroid is built up from a circuit, one unit of nullity at a time (an ear decomposition).
--
--   **Formalization Note** The chain is a function $N:\mathbb N\to$ sets whose values at indices $1,\dots,n$ are the matroids $M_1,\dots,M_n$ of the paper; its values at other indices are irrelevant. $X$ is a subset of the ground set of an ambient finite matroid (Whitney's matroid $M$ is the submatroid $X$). Nullity is computed in $\mathbb Z$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 520, Theorem 17

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_nullity

namespace WhitneyMatroid.Components

theorem nonSeparable_ear_decomposition {α : Type*} (M : Matroid α) [M.Finite]
    (X : Set α) (n : ℕ) (hX : IsNonSeparable M X) (hn : 0 < n) (hnull : nullity M X = n) :
    ∃ N : ℕ → Set α,
      M.IsCircuit (N 1) ∧ N n = X ∧
      (∀ i, 1 ≤ i → i ≤ n → IsNonSeparable M (N i) ∧ nullity M (N i) = i) ∧
      (∀ i, 1 ≤ i → i < n → N i ⊆ N (i + 1) ∧
        ∃ P : Set α, M.IsCircuit P ∧ P ⊆ N (i + 1) ∧ N (i + 1) \ N i ⊆ P ∧
          (P ∩ N i).Nonempty) := by sorry

end WhitneyMatroid.Components
