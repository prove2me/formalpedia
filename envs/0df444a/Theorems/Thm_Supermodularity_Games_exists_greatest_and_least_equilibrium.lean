-- Prove2me | Theorems.Thm_Supermodularity_Games_exists_greatest_and_least_equilibrium
-- name    : Supermodularity.Games.exists_greatest_and_least_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:33:16.066699+00:00
-- url     : https://prove2.me/theorems/fbd6abeb-dfb4-4afb-a8d0-85f393a41843
-- title:
--   Theorem 4.2.1 - the set of equilibrium points of a supermodular game is a complete lattice
-- statement:
--   Let $(N, S, \{f_i : i \in N\})$ be a **supermodular game** for which $S$, the set of
--   feasible joint strategies, is nonempty and compact, and each payoff $f_i(y_i,
--   x_{-i})$ is upper semicontinuous in $y_i$ on $S_i(x_{-i})$ for every $x_{-i} \in
--   S_{-i}$ and every player $i$. Then the set of equilibrium points is nonempty; it has
--   a greatest element and a least element; and, under the order it inherits from
--   $\mathbb{R}^m$, it is itself a **nonempty complete lattice**: every nonempty family
--   of equilibrium points has a least upper bound and a greatest lower bound *among the
--   equilibrium points*.
--
--   This is Theorem 4.2.1. Topkis [1979] establishes the existence of a greatest and a
--   least equilibrium point; Zhou [1994] further shows the equilibrium set is a complete
--   lattice. The book's proof: $S$ compact and a sublattice of $\mathbb{R}^m$ makes $S$ a
--   complete lattice (Theorem 2.3.1); the best joint response correspondence $Y$ is
--   increasing and subcomplete-valued (Lemma 4.2.2, milestone
--   `bestJointResponse_compact_and_increasing`); Theorem 2.5.1(b) (chunk `01-lattices`)
--   then gives that $Y$'s fixed points form a nonempty complete lattice with a greatest
--   and least element; and Lemma 4.2.1 (milestone `equilibrium_iff_fixed_point`)
--   identifies those fixed points with the equilibrium points.
--
--   **Formalization Note** "The set of equilibrium points is a nonempty complete
--   lattice" is formalized, as in Theorem 2.5.1 of chunk `01-lattices`, via `IsLUB`/
--   `IsGLB` on the subtype of equilibrium points — not as membership of the *ambient*
--   $\mathbb{R}^m$-supremum/infimum in the equilibrium set, which Examples 4.2.1 and
--   4.2.2 in the book show can fail (the equilibrium set need be neither compact nor a
--   sublattice of $\mathbb{R}^m$ when $n > 1$). This is the trivializing formalization
--   the chunk brief warns against ruling out: the mission does **not** state or prove
--   that the equilibrium set is compact or a sublattice of the ambient space, only that
--   it is a complete lattice under its own inherited order. The case $n = 1$ (a single
--   player maximizing a supermodular function, which the book notes reduces to Corollary
--   2.7.1 and is not this theorem's content) is not treated as a special case anywhere
--   in the statement; the theorem is stated for a general finite player set `ι`,
--   including `n = 1`, exactly as the book states it.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 181, Theorem 4.2.1

import Mathlib
import Definitions.Def_Supermodularity_Games_IsSupermodularGame
import Definitions.Def_Supermodularity_Games_IsEquilibrium

namespace Supermodularity.Games

theorem exists_greatest_and_least_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (hgame : IsSupermodularGame S f) (hSne : S.Nonempty) (hScompact : IsCompact S)
    (husc : ∀ i (x : ∀ i, Fin (m i) → ℝ),
      UpperSemicontinuousOn (fun y : Fin (m i) → ℝ => f i (Function.update x i y))
        {y : Fin (m i) → ℝ | Function.update x i y ∈ S}) :
    {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'}.Nonempty ∧
    (∃ g, IsGreatest {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} g) ∧
    (∃ l, IsLeast {x' : ∀ i, Fin (m i) → ℝ | IsEquilibrium S f x'} l) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsLUB F b) ∧
    (∀ F : Set {x' : ∀ i, Fin (m i) → ℝ // IsEquilibrium S f x'}, F.Nonempty → ∃ b, IsGLB F b) := by sorry

end Supermodularity.Games
