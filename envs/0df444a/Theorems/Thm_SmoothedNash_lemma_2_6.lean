-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_6
-- name    : SmoothedNash.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:00.707199+00:00
-- url     : https://prove2.me/theorems/20b5f74a-c248-403c-90cd-f3b9ec4c9139
-- title:
--   Lemma 2.6 — the exact equilibrium remains covered: some $c_t \in F_t(A)$ has $x^\star \in B_A(c_t,\rho_t)$ for $t \le D$
-- statement:
--   Let $u$ be a game with payoffs in $[0, 1]$, let $x^\star$ be an exact Nash equilibrium of $u$ and let $A$ be its support profile. Let $\varepsilon \in (0, 1]$ and $D = \lceil \log_2(4m/\varepsilon) \rceil$. In Algorithm 2, unless a point has already been returned, for every $t = 0, 1, \dots, D$ there is a center $c_t \in F_t(A)$ with $x^\star \in B_A(c_t, \rho_t)$:
--   1. for $t = 0$: $\|x^\star - b_A\|_1 \le \rho_0$, where $F_0(A) = \{b_A\}$;
--   2. for $1 \le t \le D$: some $c_t \in F_t(A)$ satisfies $\|x^\star - c_t\|_1 \le \rho_t$.
--
--   Together with Lemma 2.5 this shows that the frontier of the correct support guess contains a passing center at the last level.
--
--   Differences from the source:
--   - encoding: x⋆ an exact Nash equilibrium (ε = 0 in the pure-deviation definition, p.6) → AGT.IsMixedNash u xs (no profitable deviation to any lottery); reason: for mixed profiles the two are equivalent (a lottery deviation is a convex combination of pure ones)
--   - encoding: A the support profile of x⋆ → a support profile A with A_i = {a : x⋆_i(a) > 0} (hypothesis hA); reason: the definition of the support profile
--   - encoding: games with payoffs u_i : [n]^m → [0, 1] (p.6) → real payoffs u with the hypothesis PayoffsIn01 u; reason: the range [0, 1] is part of the paper's game model and is stated as a hypothesis
--   - encoding: F_t(A) and N_t(A) := |F_t(A)|, the centers that would be tested if the algorithm continued after any earlier return (p.14) → frontier u A t, an order-free Finset of numerator vectors; reason: the frontier is a set, so it does not depend on the processing order; numerator vectors are in bijection with the grid points (Lemma 2.1)
--   - encoding: x⋆ ∈ B_A(c_t, ρ_t) → ‖x⋆ − c_t‖₁ ≤ ρ_t; reason: x⋆ ∈ K_A holds because A is its support profile
--   - generalization: a game with m players, each with n actions (m, n ≥ 1 implicit) → any m, n ∈ ℕ, including 0; reason: the statement specializes to m, n ≥ 1; for m = 0 or n = 0 the instance is degenerate (the hypotheses are unsatisfiable or the claim is immediate)
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.6, p.17

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_PayoffsIn01
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_l1
import Definitions.Def_SmoothedNash_rho
import Definitions.Def_SmoothedNash_D
import Definitions.Def_SmoothedNash_gridPt
import Definitions.Def_SmoothedNash_bary
import Definitions.Def_SmoothedNash_frontier

namespace SmoothedNash

/-- **Lemma 2.6 (The exact equilibrium remains covered)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.17). Let `x⋆` be an exact Nash
equilibrium of the realized game (payoffs in `[0, 1]`) and let `A` be its support profile. In
Algorithm 2, unless a point has already been returned, for every `t = 0, 1, …, D` there exists a
center `c_t ∈ F_t(A)` with `x⋆ ∈ B_A(c_t, ρ_t)`.

The conjunction states the case `t = 0` (`F_0(A) = {b_A}`) and the cases `1 ≤ t ≤ D`.

**Formalization Note** The frontiers `F_t(A)` are the order-free sets `frontier u A t` of the
centers that would be tested if the algorithm continued after any earlier return (p.14), which is
the meaning of "unless a point has already been returned". -/
theorem lemma_2_6 {m n : ℕ} (u : Game m n) (hu : PayoffsIn01 u) (xs : Fin m → Fin n → ℝ)
    (hxs : AGT.IsMixedNash (S := fun _ : Fin m => Fin n) u xs) (A : SupportProfile m n)
    (hA : ∀ i a, a ∈ A.1 i ↔ 0 < xs i a) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    l1 xs (bary A) ≤ rho m 0 ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ D m ε → ∃ k ∈ frontier u A t, l1 xs (gridPt A t k) ≤ rho m t := by sorry

end SmoothedNash
