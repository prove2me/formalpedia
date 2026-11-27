-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_Supplement_proof_theorem_1_step_one
-- name    : TailOptCaching.ETLRU.Supplement.proof_theorem_1_step_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:48:56.85333+00:00
-- url     : https://prove2.me/theorems/b5cc32f0-3ceb-4f12-9ab1-02e736e4ec8c
-- title:
--   Proof of Theorem 1, Step one (corrected: integer threshold ξ; capping is free rather than forced) — problem (7) is equivalent to the capped max-hits problem (11)–(12)
-- statement:
--   Fix a deterministic trace with $N$ conversations, request-time sets $\mathcal T_i\subseteq[T]$ and turn lengths $q_{i,t},a_{i,t}$, a capacity $C\in\mathbb N$ and an integer threshold $\xi\in\mathbb N$. Write $B_{i,t}=\sum_{j\le t}q_{i,j}+\sum_{j<t}a_{i,j}$ for the blocks needed by the request of $i$ at $t$, $\mathrm{TEL}(x)=\sum_i\sum_{t\in\mathcal T_i}(B_{i,t}-x_{i,t}-\xi)^+$, $\mathrm{hits}(x)=\sum_i\sum_{t\in\mathcal T_i}x_{i,t}$, and call $x$ feasible when it satisfies (4)–(6) from the empty cache. Then:
--
--   1. **Optimal slacks.** For every caching state $x$ and every $u$ with $u_{i,t}\in\mathbb N$ and $u_{i,t}\ge B_{i,t}-x_{i,t}-\xi$ at every request, $\mathrm{TEL}(x)\le\sum_i\sum_{t\in\mathcal T_i}u_{i,t}$. Since $u_{i,t}=(B_{i,t}-x_{i,t}-\xi)^+$ is admissible, the value of (7) is $\min_x\mathrm{TEL}(x)$ over feasible $x$.
--   2. **Capping is free.** If $x$ is feasible, then the capped state $\bar x$, with $\bar x_{i,t}=\min\bigl(x_{i,t},(B_{i,t}-\xi)^+\bigr)$ for $t\in\mathcal T_i$ and $\bar x_{i,t}=x_{i,t}$ otherwise, is feasible, satisfies the TEL-safe budget (12), and has $\mathrm{TEL}(\bar x)=\mathrm{TEL}(x)$.
--   3. **Objective identity.** If $x$ satisfies (12), then
--   $$\mathrm{TEL}(x)+\mathrm{hits}(x)=\sum_{i\in[N]}\sum_{t\in\mathcal T_i}\bigl(B_{i,t}-\xi\bigr)^+ .$$
--   4. **Equivalence of the problems.** If $x$ is feasible and satisfies (12), then $x$ maximizes $\mathrm{hits}$ over the states feasible for (4)–(6) and (12) — problem (11)–(12) — if and only if $x$ minimizes $\mathrm{TEL}$ over all feasible states — problem (7).
--
--   This is the first step of the paper's proof of Theorem 1: it turns the latency objective into a count of reused blocks under a per-request cap, the form in which the furthest-in-future argument of the second step applies.
--
--   **Formalization Note** The trace, feasibility, TEL, hits and the TEL-safe budget are those of `TailOptCaching.ETLRU.Supplement.Trace`. Positive parts are `Int.toNat`; the constant $\alpha$ is dropped. Clause 3 is written as a sum, not a difference, so no natural-number subtraction appears.
--
--   Differences from the source:
--   - correction: threshold ξ = ξ_s/α ≥ 0 real → ξ ∈ ℕ; reason: with fractional ξ the claim is false (one conversation, requests at t = 1 with q = 1, a = 0 and t = 2 with q = 0, C = 5, ξ = 1/2: the least TEL is 1/2, attained only above the budget, but Σ b⁺ − max (11)–(12) = 1); the source measures every length in blocks and takes u ∈ ℕ in (7)
--   - correction: "the optimal solution to (7) must satisfy the TEL-safe budget" → capping any feasible solution keeps it feasible and leaves TEL unchanged (clause 2); reason: with slack capacity an optimal solution may exceed the budget (cache everything), so the literal claim is false; the proof's argument shows exactly clause 2
--   - reading: x_{i,1} unconstrained → x_{i,1} = 0 (empty initial cache); reason: the prose of (5) bounds the cache by the history up to time t, which is empty before the first request
--   - encoding: "min (7) is a constant minus max (11)" → the identity TEL + hits = Σ budget on capped states and the equivalence of optimizers (clauses 3–4); reason: same content without subtraction in ℕ
--   - encoding: TEL = α Σ (·)⁺ → Σ (·)⁺; reason: the factor α > 0 changes no minimizer
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, p. 16, App. A, Proof of Theorem 1, Step one: Equivalence of Optimization Problems, (11)–(12); p. 6, problem (7); p. 5, constraints (4)–(6)

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Supplement_Trace

namespace TailOptCaching.ETLRU.Supplement

theorem proof_theorem_1_step_one {N : ℕ} (tr : Trace N) (C ξ : ℕ) :
    (∀ (x u : Fin N → ℕ → ℕ),
        (∀ i t, t ∈ reqTimes tr i → (need tr i t : ℤ) - x i t - ξ ≤ u i t) →
        tel tr ξ x ≤ ∑ i, ∑ t ∈ reqTimes tr i, u i t) ∧
    (∀ x, Feasible tr C x →
        Feasible tr C (capToBudget tr ξ x) ∧ WithinBudget tr ξ (capToBudget tr ξ x) ∧
          tel tr ξ (capToBudget tr ξ x) = tel tr ξ x) ∧
    (∀ x, WithinBudget tr ξ x →
        tel tr ξ x + hits tr x = ∑ i, ∑ t ∈ reqTimes tr i, budget tr ξ i t) ∧
    (∀ x, Feasible tr C x → WithinBudget tr ξ x →
        ((∀ y, Feasible tr C y → WithinBudget tr ξ y → hits tr y ≤ hits tr x) ↔
          (∀ y, Feasible tr C y → tel tr ξ x ≤ tel tr ξ y))) := by sorry

end TailOptCaching.ETLRU.Supplement
