-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_4
-- name    : SmoothedNash.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:56.111007+00:00
-- url     : https://prove2.me/theorems/87ba3c60-1591-4fd6-9d02-73cdd00c455a
-- title:
--   Lemma 2.4 — a center that passes the level-$t$ test is a $2\rho_t$-Nash equilibrium
-- statement:
--   Let $u$ be a game, $A$ a support profile and $t \ge 0$. If a level-$t$ candidate center $c \in K_A$ passes the level-$t$ test (tolerance $2\rho_t$), then $c$ is a $2\rho_t$-approximate Nash equilibrium:
--   $$
--   u_i(a, c_{-i}) \le u_i(c) + 2\rho_t \qquad \text{for all } i \in [m],\ a \in [n].
--   $$
--   This is why any point returned at the last level $D$ is an $\varepsilon$-Nash equilibrium.
--
--   Differences from the source:
--   - generalization: a level-t candidate center c ∈ K_A → every c ∈ K_A; reason: candidates of Algorithm 2 are points of K_A, so the statement specializes to them
--   - generalization: games with payoffs in [0, 1] (p.6) → every real-valued game; reason: the proof uses no bound on the payoffs; the statement specializes to games with payoffs in [0, 1]
--   - generalization: a game with m players, each with n actions (m, n ≥ 1 implicit) → any m, n ∈ ℕ, including 0; reason: the statement specializes to m, n ≥ 1; for m = 0 or n = 0 the instance is degenerate (the hypotheses are unsatisfiable or the claim is immediate)
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.4, p.16

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_IsEpsNash
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_InK
import Definitions.Def_SmoothedNash_rho
import Definitions.Def_SmoothedNash_PassesTest

namespace SmoothedNash

/-- **Lemma 2.4 (A candidate that passes the test is already approximate)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.16). If a
level-`t` candidate center `c ∈ K_A` passes the level-`t` test, then `c` is a `2ρ_t`-approximate Nash
equilibrium.

**Formalization Note** A level-`t` candidate center is any `c ∈ K_A`, tested with tolerance `2ρ_t`. -/
theorem lemma_2_4 {m n : ℕ} (u : Game m n) (A : SupportProfile m n) (t : ℕ)
    (c : Fin m → Fin n → ℝ) (hc : InK A c) (hpass : PassesTest u A (2 * rho m t) c) :
    IsEpsNash u (2 * rho m t) c := by sorry

end SmoothedNash
