-- Prove2me | Theorems.Thm_SmoothedNash_lemma_2_3
-- name    : SmoothedNash.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:00.630335+00:00
-- url     : https://prove2.me/theorems/7cff9f48-6e22-461e-b371-245d5df648ef
-- title:
--   Lemma 2.3 — Lipschitzness of deviation payoffs: $|U_{i,a}(x) - U_{i,a}(y)| \le \sum_{j \ne i}\|x_j - y_j\|_1$
-- statement:
--   Let $u$ be a game with payoffs in $[0, 1]$. For every player $i$, action $a \in [n]$ and mixed profiles $x, y \in (\Delta_n)^m$,
--   $$
--   |U_{i,a}(x) - U_{i,a}(y)| \le \sum_{j \ne i} \|x_j - y_j\|_1 .
--   $$
--   In particular, if $c \in K_A$ is a level-$t$ candidate and $y \in B_A(c, \rho_t)$, then
--   $$
--   |U_{i,a}(c) - U_{i,a}(y)| \le \rho_t = 2m\,2^{-t} \qquad \text{for every } i \in [m],\ a \in [n].
--   $$
--   This is the continuity estimate behind every survival argument of Section 2 (Lemmas 2.5 and 2.9).
--
--   Differences from the source:
--   - encoding: games with payoffs u_i : [n]^m → [0, 1] (p.6) → real payoffs u with the hypothesis PayoffsIn01 u; reason: the range [0, 1] is part of the paper's game model and is stated as a hypothesis
--   - generalization: a level-t candidate center c ∈ K_A → every c ∈ K_A; reason: candidates of Algorithm 2 are points of K_A, so the statement specializes to them
--   - generalization: a game with m players, each with n actions (m, n ≥ 1 implicit) → any m, n ∈ ℕ, including 0; reason: the statement specializes to m, n ≥ 1; for m = 0 or n = 0 the instance is degenerate (the hypotheses are unsatisfiable or the claim is immediate)
--   - encoding: players [m] and actions [n], numbered from 1 → Fin m and Fin n, numbered from 0; reason: Lean indexing; same games
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.3, pp.15–16

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_devPayoff
import Definitions.Def_SmoothedNash_PayoffsIn01
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_InK
import Definitions.Def_SmoothedNash_l1
import Definitions.Def_SmoothedNash_rho

namespace SmoothedNash

/-- **Lemma 2.3 (Lipschitzness of deviation payoffs)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.15–16). For a game with payoffs in
`[0, 1]`, every player `i`, action `a ∈ [n]` and mixed profiles `x, y ∈ (Δ_n)^m`,
`|U_{i,a}(x) − U_{i,a}(y)| ≤ Σ_{j ≠ i} ‖x_j − y_j‖_1`. In particular, if `c` is a level-`t`
candidate and `y ∈ B_A(c, ρ_t)`, then `|U_{i,a}(c) − U_{i,a}(y)| ≤ ρ_t` for every `i, a`.

**Formalization Note** A level-`t` candidate is any `c ∈ K_A` (the candidates of Algorithm 2 lie in
`K_A`), and `y ∈ B_A(c, ρ_t)` is `y ∈ K_A ∧ ‖y − c‖_1 ≤ ρ_t`. -/
theorem lemma_2_3 {m n : ℕ} (u : Game m n) (hu : PayoffsIn01 u) :
    (∀ x y : Fin m → Fin n → ℝ, AGT.IsMixedProfile (S := fun _ : Fin m => Fin n) x →
      AGT.IsMixedProfile (S := fun _ : Fin m => Fin n) y → ∀ (i : Fin m) (a : Fin n),
        |devPayoff u x i a - devPayoff u y i a| ≤ ∑ j ∈ Finset.univ.erase i, ∑ b, |x j b - y j b|) ∧
    (∀ (A : SupportProfile m n) (t : ℕ) (c y : Fin m → Fin n → ℝ), InK A c → InK A y →
      l1 y c ≤ rho m t → ∀ (i : Fin m) (a : Fin n),
        |devPayoff u c i a - devPayoff u y i a| ≤ rho m t) := by sorry

end SmoothedNash
