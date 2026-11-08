-- Prove2me | Theorems.Thm_StatefulPricing_section_3_1_induced
-- name    : StatefulPricing.section_3_1_induced
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T08:26:23.94628+00:00
-- url     : https://prove2.me/theorems/2a119050-965a-4615-a757-e97a6bba8a8a
-- title:
--   §3.1, Eq. (4): DRACC is a Dd-MDP — policy simulations and revenues coincide
-- statement:
--   Let $I$ be a DRACC instance and consider its induced Dd-MDP (states $(A,\lambda)$, actions price vectors, reward $f_t(s,x)=\hat q^x_t$, transition to $(A_{t+1},\lambda')$). Then:
--
--   1. the induced rewards lie in $[0,1]$ on feasible state–action pairs;
--   2. for every pricing policy $\gamma$ and every round $t\ge1$, the simulation of $\gamma$ in the Dd-MDP (Eq. (2)) is at the state $(A_t,\lambda^\gamma_t)$;
--   3. for every pricing policy $\gamma$,
--   $$
--   \sum_{t=1}^T f_t\big(s^\gamma(t),x^\gamma(t)\big)=\sum_{t=1}^T\hat q^{\gamma}_t;
--   $$
--   4. for every sequence of price vectors $p_1,p_2,\dots$, the states visited by playing it in the Dd-MDP are $(A_t,\lambda_t)$, where $\lambda_t$ is the DRACC inventory along $p$, and the total Dd-MDP reward over $[1,T]$ equals the DRACC revenue $\sum_{t=1}^T\hat q^{p_t}_t$.
--
--   This is the translation "the notion of (pricing) policies and their recursive simulations and the notion of regret translate directly from the DRACC setting to that of Dd-MDPs", which lets the Dd-MDP results apply to posted pricing.
--
--   Differences from the source:
--   - reading: "the notion of (pricing) policies and their recursive simulations and the notion of regret translate directly" → the four identities above (bounded rewards, states, policy rewards, open-loop rewards); reason: they are what the translation is used for in the proof of Theorem 3.10
--   - encoding: resources $[N]$, vectors indexed by $A_t$, prices in $(0,1]^{A_t}$ → resources are a finite set of natural numbers, inventory vectors $\mathbb N\to\mathbb N$ equal to $0$ off $A_t$, price vectors $\mathbb N\to\mathbb R$ with values in $(0,1]$ at every resource; reason: changes no demand set, payment or inventory
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, §3.1, p.7, Eq. (4)

import Mathlib
import Definitions.Def_StatefulPricing_DdMDP
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Instance_toDdMDP

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **DRACC is a Dd-MDP** (arXiv:2005.01869v2, §3.1, p.7, Eq. (4) and the transition display):
"Given the aforementioned definitions, the notion of (pricing) policies and their recursive
simulations and the notion of regret translate directly from the DRACC setting to that of
Dd-MDPs."

For every DRACC instance `I`:
1. the induced Dd-MDP has rewards in `[0,1]` on feasible state–action pairs;
2. the simulation (Eq. (2)) of every policy `γ` visits the state `(A_t, λ^γ_t)` at every round
   `t ≥ 1`;
3. the cumulative reward of that simulation over `[1,T]` is the revenue `Σ_{t=1}^T q̂^γ_t` of `γ`;
4. for every sequence of price vectors `p`, the states visited by playing `p` are
   `(A_t, λ_t)`, where `λ_t` is the DRACC inventory along `p`, and the total Dd-MDP reward over
   `[1,T]` is the DRACC revenue `Σ_{t=1}^T q̂^{p_t}_t`.

**Formalization Note.** The DRACC objects (`policyInv`, `traj`, `ruleRevenue`) are defined
directly from §2, not through the Dd-MDP, so items 2–4 are statements about two recursions. -/
theorem section_3_1_induced {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W) :
    (I.toDdMDP rank).RewardsInUnit ∧
    (∀ γ : Policy, ∀ t, 1 ≤ t →
      (I.toDdMDP rank).simState γ t = (I.active t, I.policyInv rank γ t)) ∧
    (∀ γ : Policy, (I.toDdMDP rank).policyReward γ T = I.policyRevenue rank γ) ∧
    (∀ p : ℕ → ℕ → ℝ,
      (∀ t, 1 ≤ t → (I.toDdMDP rank).actState p t = (I.active t, I.traj rank (fun s _ => p s) t)) ∧
      ∑ t ∈ Finset.Icc 1 T, (I.toDdMDP rank).f t ((I.toDdMDP rank).actState p t) (p t)
        = I.ruleRevenue rank (fun s _ => p s)) := by sorry

end StatefulPricing
