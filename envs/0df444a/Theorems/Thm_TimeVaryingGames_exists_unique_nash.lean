-- Prove2me | Theorems.Thm_TimeVaryingGames_exists_unique_nash
-- name    : TimeVaryingGames.exists_unique_nash
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:23.660728+00:00
-- url     : https://prove2.me/theorems/31307b97-b195-41a7-8ef1-d82683717354
-- title:
--   Theorem 1, p.10, "(necessarily unique)": a strictly monotone game has exactly one Nash equilibrium
-- statement:
--   Consider a continuous game with a finite nonempty set of players, nonempty compact convex action sets $\mathcal K_i$ in finite-dimensional normed spaces, and payoffs continuously differentiable on an open neighbourhood of $\mathcal K$. If the game is strictly monotone,
--   $$\langle v(x')-v(x),x'-x\rangle<0\qquad(x,x'\in\mathcal K,\ x'\ne x),$$
--   then it has exactly one Nash equilibrium.
--
--   This is the content of the words "the (necessarily unique) Nash equilibrium $x^*$ of $\mathcal G$" in Theorem 1: the limit game of Theorem 1 has an equilibrium, and only one, so the conclusion of Theorem 1 names a well-defined point.
--
--   Differences from the source:
--   - reading: "the (necessarily unique) Nash equilibrium x∗ of G" → ∃! xs, IsNash K u xs; reason: the definite article asserts existence and the parenthesis uniqueness
--   - encoding: u_i tacitly defined on an open neighbourhood of K (p.4) → an explicit open set U ⊇ K on which u_i is C¹; reason: the paper's own device, made explicit
--   - encoding: N = {1, …, N} players, compact convex K_i → Nonempty ι (and, where existence matters, nonempty K_i); reason: nondegeneracy implicit in the paper: a game has a player and every player has an action
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, Theorem 1, p.10 ("the (necessarily unique) Nash equilibrium x* of G"); strictly monotone, p.5

import Mathlib
import Definitions.Def_TimeVaryingGames_ContinuousGame

namespace TimeVaryingGames

/-- **A strictly monotone game has exactly one Nash equilibrium.**
arXiv:1809.03066v3, Theorem 1, p.10: "Then, with probability 1, the sequence of realized actions
X_t converges to the (necessarily unique) Nash equilibrium x* of G." The parenthesis asserts that
the strictly monotone limit game `G` has a Nash equilibrium and that it is unique (§2.3, p.4–5;
Rosen [50]).

Setting of §2.2: finitely many players (at least one), each with a nonempty compact convex action
set `K_i` in a finite-dimensional normed space; payoffs continuously differentiable on an open
neighbourhood `U` of the action space; the game is strictly monotone (DC strict, p.5). -/
theorem exists_unique_nash {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKne : ∀ i, (K i).Nonempty) (hKc : ∀ i, IsCompact (K i))
    (hKcv : ∀ i, Convex ℝ (K i))
    (U : Set (∀ j, E j)) (hU : IsOpen U) (hKU : profiles K ⊆ U)
    (u : ι → (∀ j, E j) → ℝ) (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (hmono : IsStrictlyMonotone K u) :
    ∃! xs, IsNash K u xs := by sorry

end TimeVaryingGames
