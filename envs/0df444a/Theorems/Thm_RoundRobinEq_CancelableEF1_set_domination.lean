-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableEF1_set_domination
-- name    : RoundRobinEq.CancelableEF1.set_domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:16.507708+00:00
-- url     : https://prove2.me/theorems/b8afb4b6-5e68-4f13-8ac0-871b21161daf
-- title:
--   §4.2, p. 21 — v_i({x_1, …, x_{τ_ℓ}}) ≥ v_i(Y_ℓ) for the truthful deviation
-- statement:
--   In the setting of inequality (2) for the truthful deviation: $\succ$ is a profile of rankings with $m = kn$ goods, agent $i$ has a cancelable valuation $v_i$ and deviates to a strict truthful ranking $\succ'_i$, $x_r$ is the good $i$ receives in round $r$ of Round-Robin$(\succ'_i, \succ_{-i})$, and for an agent $j \neq i$ the bundle $A_j = \{y_1, \dots, y_k\}$ of Round-Robin$(\succ)$ is indexed by allocation time in Round-Robin$(\succ'_i, \succ_{-i})$, with $Y_1 = \{y_3, y_5, \dots\}$, $Y_2 = \{y_2, y_4, \dots\}$ and $\tau_\ell = |Y_\ell|$. Then for $\ell \in \{1, 2\}$,
--   $$v_i(\{x_1, x_2, \dots, x_{\tau_\ell}\}) \ge v_i(Y_\ell).$$
--
--   This is the step of the proof of Theorem 4.5 that converts the round-by-round comparison into a comparison of sets; together with subadditivity and the equilibrium condition it bounds $v_i(A_j \setminus \{y_1\})$.
--
--   **Formalization Note** The page derives this inequality from (2) through an intermediate claim, $v_i(x_r) \ge v_i(y^\ell_r)$, attributed to cancelability, and then Lemma 3.3. That intermediate claim needs $y^\ell_r \notin \{x_1, \dots, x_{r-1}\}$ and is false in general (an instance with additive valuations, $n = 2$, $m = 8$, violates it); the inequality stated here was not violated in any of the tested instances, but its derivation on the page is incomplete. No equilibrium hypothesis is assumed. The prefix $\{x_1, \dots, x_{\tau_\ell}\}$ is `xPrefix x |Y_ℓ|`; $m = kn$ is a hypothesis.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 21, proof of Theorem 4.5, second paragraph ("Now we apply Lemma 3.3 to get …")

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableEF1_Setting
import Definitions.Def_RoundRobinEq_CancelableEF1_DeviationOrders

namespace RoundRobinEq.CancelableEF1

/-- The set domination asserted in the proof of Theorem 4.5 (Amanatidis et al.,
arXiv:2301.13652v1, §4.2, p. 21): in the setting of inequality (2) for the truthful deviation,
`v_i({x_1, …, x_{τ_ℓ}}) ≥ v_i(Y_ℓ)` for `ℓ ∈ {1, 2}`, where `τ_ℓ = |Y_ℓ|`. The renamings of `Y_1`,
`Y_2` do not enter the statement. No equilibrium hypothesis is needed. -/
theorem set_domination {M : Type*} [DecidableEq M] [Fintype M] {n : ℕ} [NeZero n]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (v : Fin n → Finset M → ℝ) (i j : Fin n) (hji : j ≠ i)
    (hvi : RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ RoundRobinEq.CancelableBluff.IsCancelable (v i))
    (σ : Fin n → List M) (hσ : ∀ ℓ, RoundRobinEq.CancelableBluff.IsRanking (σ ℓ))
    (τ : List M) (hτ : IsStrictTruthfulFor (v i) τ)
    (x y : ℕ → M)
    (hx : IsRoundEnum (Function.update σ i τ) i k x)
    (hy : IsTimeEnum (Function.update σ i τ) (roundRobin σ j) k y) :
    v i (Y1 y k) ≤ v i (xPrefix x (Y1 y k).card) ∧
      v i (Y2 y k) ≤ v i (xPrefix x (Y2 y k).card) := by sorry

end RoundRobinEq.CancelableEF1
