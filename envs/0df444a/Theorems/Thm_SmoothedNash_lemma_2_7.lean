-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_7
-- name    : SmoothedNash.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:50.49037+00:00
-- url     : https://prove2.me/theorems/7ef891a3-464e-4bd6-9b47-5ee039277236
-- title:
--   Lemma 2.7 — correctness: Algorithm 2 always returns a point, and it is an $\varepsilon$-Nash equilibrium
-- statement:
--   Let $u$ be a game with $m \ge 1$ players, $n \ge 1$ actions and payoffs in $[0, 1]$, and let $\varepsilon \in (0, 1]$. For every processing order of the support profiles and of the frontiers:
--   1. whenever Algorithm 2 returns a point, that point is an $\varepsilon$-approximate Nash equilibrium;
--   2. Algorithm 2 returns a point (it does not return Fail).
--
--   This is the correctness half of Theorem 2.2; it holds for every game, with no randomness.
--
--   Differences from the source:
--   - reading: "for all support profiles" (line 2) and "for all c ∈ F_t(A)" (line 9), with no order fixed → every support order σ and every frontier enumeration; reason: the pseudocode fixes no order, and the lemma holds for each
--   - encoding: the algorithm's output, a point or Fail → RunResult.out : Option, with none for Fail; reason: Lean representation of a possibly failing output
--   - encoding: games with payoffs u_i : [n]^m → [0, 1] (p.6) → real payoffs u with the hypothesis PayoffsIn01 u; reason: the range [0, 1] is part of the paper's game model and is stated as a hypothesis
--   - encoding: a game with m players, each with n actions (m, n ≥ 1 implicit) → hypotheses 1 ≤ m and 1 ≤ n; reason: a game has a player, and Δ_n is empty for n = 0
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.7, p.17

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_IsEpsNash
import Definitions.Def_SmoothedNash_PayoffsIn01
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_IsSupportOrder
import Definitions.Def_SmoothedNash_IsFrontierEnum
import Definitions.Def_SmoothedNash_run

namespace SmoothedNash

/-- **Lemma 2.7 (Correctness of any returned output)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.17). Whenever Algorithm 2 returns a
point, that point is an `ε`-approximate Nash equilibrium. Moreover, for every realized game,
Algorithm 2 returns a point.

Stated for every game with `m ≥ 1` players, `n ≥ 1` actions and payoffs in `[0, 1]`, every
`ε ∈ (0, 1]`, and every processing order of the supports (`σ`) and of the frontiers (`enum`).

**Formalization Note** The pseudocode fixes no processing order, so the lemma is stated for every
order. -/
theorem lemma_2_7 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (u : Game m n) (hu : PayoffsIn01 u)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (σ : List (SupportProfile m n)) (hσ : IsSupportOrder σ)
    (enum : SupportProfile m n → Finset (Fin m → Fin n → ℕ) → List (Fin m → Fin n → ℕ))
    (henum : IsFrontierEnum enum) :
    (∀ x, (run u ε enum σ).out = some x → IsEpsNash u ε x) ∧ (run u ε enum σ).out ≠ none := by sorry

end SmoothedNash
