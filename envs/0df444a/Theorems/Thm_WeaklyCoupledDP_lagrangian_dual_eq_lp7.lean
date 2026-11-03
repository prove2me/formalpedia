-- Prove2me | Theorems.Thm_WeaklyCoupledDP_lagrangian_dual_eq_lp7
-- name    : WeaklyCoupledDP.lagrangian_dual_eq_lp7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:47.272624+00:00
-- url     : https://prove2.me/theorems/598253f6-d16b-4acd-9da4-7fd088cff768
-- title:
--   §3.2.1 — the Lagrangian dual $V^{\lambda*}_1(s_1,e_1)$ equals the optimal value of LP (7)
-- statement:
--   The Lagrangian dual problem $V^{\lambda*}_1(s_1,e_1) = \min_{\lambda \in \Lambda} V^\lambda_1(s_1,e_1)$ equals the optimal value of the linear program (7). Precisely:
--
--   1. every feasible solution $(\lambda, W)$ of (7) has $\lambda \in \Lambda$ and objective value at least $V^\lambda_1(s_1,e_1)$:
--   $$
--   V^\lambda_1(s_1,e_1) \le \sum_{t=1}^T \mathbb E_{e_t}\big[\lambda_t(e_t)^\top b_t(e_t)\big] + \sum_{i=1}^N W_{1,i}(s_{1,i},e_1);
--   $$
--   2. every $\lambda \in \Lambda$ extends to a feasible solution $(\lambda, W)$ of (7) whose objective value is exactly $V^\lambda_1(s_1,e_1)$.
--
--   Together the two clauses say that the set of objective values of (7) and the set $\{V^\lambda_1(s_1,e_1) : \lambda \in \Lambda\}$ have the same infimum, and that one minimum is attained exactly when the other is. LP (7) is how the Lagrangian dual is computed: both its number of variables and its number of constraints grow linearly in $N$.
--
--   Differences from the source:
--   - generalization: equality of the two optimal values → clauses (i) and (ii); reason: together they give the equality whenever either optimum exists, without presupposing that it does.
--   - encoding: E_{eₜ}[·] → the expectation of eₜ given e₁ computed through Q₁,…,Q_{t−1}; reason: the paper's E_{eₜ} is the expectation over eₜ from the given initial state.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §3.2.1, p.9 (PDF p.10), LP (7)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_LagrangianLPFeasible

namespace WeaklyCoupledDP

/-- **§3.2.1** (Brown & Zhang, SSRN 3849573 (Feb. 6, 2022), p.9): `V^λ*₁(s₁, e₁)` equals the optimal
value of LP (7).

**Formalization Note.** Two clauses that together give the equality of the two optimal values
without presupposing that either exists: (i) every (7)-feasible `(λ, W)` has `λ ∈ Λ` and objective
at least `V^λ₁(s₁, e₁)`; (ii) every `λ ∈ Λ` extends to a (7)-feasible `(λ, W)` with objective exactly
`V^λ₁(s₁, e₁)`. -/
theorem lagrangian_dual_eq_lp7 {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*}
    {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ} [∀ t i, Fintype (S t i)] [Fintype E]
    (M : Model N S E Act L) :
    (∀ (lam : M.Multiplier) (W : M.ValueArray), M.LagrangianLPFeasible lam W →
      lam ∈ M.Lambda ∧ M.lagrangianValue lam 1 M.s₁ M.e₁ ≤ M.lagrangianLPObjective lam W) ∧
    (∀ lam ∈ M.Lambda, ∃ W : M.ValueArray, M.LagrangianLPFeasible lam W ∧
      M.lagrangianLPObjective lam W = M.lagrangianValue lam 1 M.s₁ M.e₁) := by sorry

end WeaklyCoupledDP
