-- Prove2me | Theorems.Thm_WeaklyCoupledDP_proposition_3_2
-- name    : WeaklyCoupledDP.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:15.447986+00:00
-- url     : https://prove2.me/theorems/3261bf21-ceac-4108-bcd4-1ae0e89dbc27
-- title:
--   Proposition 3.2 — weak duality, decomposition and convexity of the Lagrangian relaxation
-- statement:
--   For every multiplier $\lambda \in \Lambda$, every period $1 \le t \le T$ and every state $(s_t,e_t)$:
--
--   1. **(Weak duality)** $V^*_t(s_t,e_t) \le V^\lambda_t(s_t,e_t)$.
--   2. **(Decomposition)** The Lagrangian value function splits into a multiplier term and the subproblem values:
--   $$
--   V^\lambda_t(s_t,e_t) = \sum_{\tau=t}^T \mathbb E_{e_\tau}\big[\lambda_\tau(e_\tau)^\top b_\tau(e_\tau) \,\big|\, e_t\big] + \sum_{i=1}^N V^\lambda_{t,i}(s_{t,i},e_t),
--   $$
--   where $V^\lambda_{t,i}$, the value function of subproblem $i$ in isolation, satisfies
--   $$
--   V^\lambda_{t,i}(s_{t,i},e_t) = \max_{a_{t,i} \in A_{t,i}(s_{t,i},e_t)} \Big\{ r_{t,i}(s_{t,i},e_t,a_{t,i}) - \lambda_t(e_t)^\top \ell_{t,i}(s_{t,i},e_t,a_{t,i}) + \mathbb E\big[V^\lambda_{t+1,i}(s_{t+1,i},e_{t+1}) \,\big|\, (s_{t,i},e_t,a_{t,i})\big] \Big\}
--   $$
--   with $V^\lambda_{T+1,i} = 0$.
--   3. **(Convexity)** $\lambda \mapsto V^\lambda_t(s_t,e_t)$ is piecewise linear and convex: it is convex, and it is the maximum of finitely many affine functions of $\lambda$.
--
--   The conditional expectation in 2 is over $e_\tau$ given $e_t$, through the kernels $Q_t,\dots,Q_{\tau-1}$. Clause 1 says each $V^\lambda_1(s_1,e_1)$ is an upper bound on the optimal value; clause 2 is what makes the Lagrangian relaxation computable subproblem by subproblem; clause 3 is the structure exploited by subgradient and cutting-plane methods for the dual.
--
--   Differences from the source:
--   - generalization: clause (c) for λ ∈ Λ → convexity and the max-of-affine representation on the whole space of multipliers; reason: the recursion is defined for every λ, and restricting to the convex set Λ gives the printed clause.
--   - reading: V* is the value of the policy problem (1), which satisfies (2) → V* is defined by the recursion (2); reason: the paper states that (2) expresses the optimal value function (p.4).
--   - encoding: "for all t" → for all 1 ≤ t ≤ T; reason: periods run over {1,…,T}, and at T+1 every value function is 0.
--   - encoding: E_{e_τ}[· | eₜ] → the sum over e' of the τ−t step transition probability from eₜ through Qₜ,…,Q_{τ−1} (Model.exoTrans); reason: this is the conditional law of e_τ given eₜ under the exogenous Markov chain of §2.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), Proposition 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model_optimalValue
import Definitions.Def_WeaklyCoupledDP_Model_lagrangianValue

open Finset Matrix

namespace WeaklyCoupledDP

/-- **Proposition 3.2** (Brown & Zhang, SSRN 3849573 (Feb. 6, 2022), p.8). For any `λ ∈ Λ`, for all
`1 ≤ t ≤ T` and `(sₜ, eₜ)`:

(a) (weak duality) `V*ₜ(sₜ, eₜ) ≤ V^λₜ(sₜ, eₜ)`;

(b) (decomposition) `V^λₜ(sₜ, eₜ) = ∑_{τ=t}^T E_{e_τ}[λ_τ(e_τ)ᵀ b_τ(e_τ) | eₜ] + ∑ᵢ V^λₜ,ᵢ(sₜ,ᵢ, eₜ)`,
where the subproblem values satisfy their Bellman equation with terminal value `0`;

(c) (convexity) `V^λₜ(sₜ, eₜ)` is piecewise linear and convex in `λ`: convex, and the maximum of
finitely many affine functions of `λ`.

**Formalization Note.** `M.exoTrans t (τ - t) e e'` is the probability of `e_τ = e'` given `eₜ = e`.
Clause (c) holds on the whole space of multipliers, which contains `Λ`. -/
theorem proposition_3_2 {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*}
    {L : ℕ → ℕ} [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L) :
    (∀ lam ∈ M.Lambda, ∀ t, 1 ≤ t → t ≤ M.T → ∀ (s : ∀ i, S t i) (e : E),
      M.optimalValue t s e ≤ M.lagrangianValue lam t s e) ∧
    (∀ lam ∈ M.Lambda,
      (∀ t, 1 ≤ t → t ≤ M.T → ∀ (s : ∀ i, S t i) (e : E),
        M.lagrangianValue lam t s e =
          ∑ τ ∈ Icc t M.T, ∑ e', M.exoTrans t (τ - t) e e' * (lam τ e' ⬝ᵥ M.b τ e') +
            ∑ i, M.subproblemValue lam t i (s i) e) ∧
      (∀ t, 1 ≤ t → t ≤ M.T → ∀ (i : Fin N) (s : S t i) (e : E),
        M.subproblemValue lam t i s e =
          maxOver (M.A t i s e) fun a =>
            M.r t i s e a - lam t e ⬝ᵥ M.ℓ t i s e a +
              M.subExp t i s e a (M.subproblemValue lam (t + 1) i)) ∧
      (∀ (i : Fin N) (s : S (M.T + 1) i) (e : E), M.subproblemValue lam (M.T + 1) i s e = 0)) ∧
    (∀ t, 1 ≤ t → t ≤ M.T → ∀ (s : ∀ i, S t i) (e : E),
      ConvexOn ℝ Set.univ (fun lam : M.Multiplier => M.lagrangianValue lam t s e) ∧
      ∃ (n : ℕ) (g : Fin (n + 1) → M.Multiplier →ₗ[ℝ] ℝ) (c : Fin (n + 1) → ℝ),
        ∀ lam : M.Multiplier,
          IsGreatest (Set.range fun j => g j lam + c j) (M.lagrangianValue lam t s e)) := by sorry

end WeaklyCoupledDP
