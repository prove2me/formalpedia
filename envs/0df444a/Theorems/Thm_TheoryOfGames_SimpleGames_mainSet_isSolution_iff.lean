-- Prove2me | Theorems.Thm_TheoryOfGames_SimpleGames_mainSet_isSolution_iff
-- name    : TheoryOfGames.SimpleGames.mainSet_isSolution_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:07:52.96419+00:00
-- url     : https://prove2.me/theorems/afe1d7bf-afb3-40ec-a89f-edd18bc135b7
-- title:
--   (50:J) — V = {α^S : S ∈ U} is a solution iff (50:8*) and (50:9*)
-- statement:
--   Let $v$ be the characteristic function (25:3:a)–(25:3:c) of a simple game in the reduced form with $\gamma = 1$ ($v((i)) = -1$, 50.4.1), $U \subseteq W^m_\Gamma$, and $x_1, \dots, x_n$ numbers with (50:7) $x_i \geqq 0$ and (50:8) $\sum_{i \in S} x_i = n$ for $S$ in $U$. Let $V$ be the set of the $\vec\alpha^S$, $S$ in $U$, and $U^+$ as in (50:G). Call a player $i$ **indifferent** when $x_i = 0$.
--
--   Then $V$ is a solution (30.1.1) if and only if
--
--   1. (50:8*) $\sum_{i \in T} x_i = n$ for the $T$ of $U$ and also for those which differ from these only by indifferent elements; and
--   2. (50:9*) for all other $T$ of $U^+$,
--   $$\sum_{i \in T} x_i > n.$$
--
--   This is the exact criterion by which a system $U$ of "profitable" minimal winning coalitions and the values $x_i$ yield a finite solution of a simple game.
--
--   **Formalization Note** "$T$ differs from a $T'$ of $U$ only by indifferent elements" is: every element of the symmetric difference of $T$ and $T'$ has $x_i = 0$. Clause 1 is implied by the standing hypothesis (50:8) and is kept because the book's criterion lists it.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 442, (50:J), (50:8*), (50:9*); p. 438, 50.5.1, (50:7), (50:8); p. 439, (50:G)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

namespace TheoryOfGames.SimpleGames

/-- (50:J), p. 442: for a simple game in the reduced form with `γ = 1` (`v((i)) = -1`), a set
`U ⊆ W^m` and numbers `xᵢ` with (50:7) `xᵢ ≧ 0` and (50:8) `∑_{i in S} xᵢ = n` for `S` in
`U`, the set `V` of the `α^S`, `S` in `U`, is a solution if and only if, calling `i`
indifferent when `xᵢ = 0`: (50:8*) `∑_{i in T} xᵢ = n` for the `T` of `U` and for those which
differ from these only by indifferent elements; and (50:9*) `∑_{i in T} xᵢ > n` for all other
`T` of `U⁺`. -/
theorem mainSet_isSolution_iff {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1)
    (U : Set (Finset (Fin n))) (hU : U ⊆ minimalSets (winningSets v))
    (x : Fin n → ℝ) (hx7 : ∀ i, 0 ≤ x i) (hx8 : ∀ S ∈ U, ∑ i ∈ S, x i = (n : ℝ)) :
    IsSolution v (mainSet U x) ↔
      ((∀ T : Finset (Fin n), (∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          ∑ i ∈ T, x i = (n : ℝ)) ∧
        (∀ T ∈ uPlus U, (¬ ∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          (n : ℝ) < ∑ i ∈ T, x i)) := by sorry

end TheoryOfGames.SimpleGames
