-- Prove2me | Theorems.Thm_SelfAdaptingFNR_corollary_1
-- name    : SelfAdaptingFNR.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:49.483439+00:00
-- url     : https://prove2.me/theorems/db4de2c2-27bd-4e45-8e59-8d43f4bd060b
-- title:
--   Corollary 1: the slack network is a feasibility network
-- statement:
--   Let a weakly coupled MDP be given and $t\in\mathcal T$ a decision period. The paths $\mathcal P_t$ of the slack network $\mathcal N_t$ of period $t$ and the feasible state–action pairs that satisfy the linking constraints form a bijection: the map sending a path to the state–action pair formed by its labels is a bijection from $\mathcal P_t$ onto $\mathscr F_t$. That is, the slack network is a feasibility network of $\mathscr F_t$.
--
--   Consequently, the network relaxation FNR can always be built on the slack network (the variant FNR(SL)).
--
--   Differences from the source:
--   - reading: a feasibility network 𝒩_t with layers 𝒱_{t,1},…,𝒱_{t,J+1}, arcs (vⱼ,sⱼ,aⱼ,vⱼ₊₁), |𝒱_{t,1}| = 1 (p.ec8), 'each node-state-action triple is unique' (p.17) → LayeredNetwork: finite layers, a unique root, arcs as a partial successor map succ j v s a : Option (V j.succ) with feasible labels aⱼ ∈ 𝒜_{t,j}(sⱼ); reason: the FNR variables y_{t,j}(v,sⱼ,aⱼ) are indexed by node–state–action triples, so a triple carries at most one arc
--   - encoding: 'each of its paths represents a feasible state–action pair of the WDP and vice versa' (p.3), 'form a bijection' (p.12) → IsFeasibilityNetwork: the map path ↦ its labels ((s₁,a₁),…,(s_J,a_J)) is injective with range 𝓕_t; reason: a bijection between 𝒫_t and 𝓕_t, written as injectivity plus range
--   - reading: 'the slacks u_{t,j} and u_{t+1,j} associated with vⱼ and vⱼ₊₁' (p.12) → the head node's slack is u_{t,j+1}; reason: printed typo: vⱼ₊₁ lies in layer j+1 of the same period
--   - encoding: layer j consists of the distinct values taken by u_{t,j} in 𝓕^V_t → layer 1 is {b}; layers 2,…,J+1 are the values of u_{t,j} over 𝓕_t; reason: u_{t,k,1} := b_k; this is the set of values of u_{t,1} over 𝓕_t whenever 𝓕_t ≠ ∅, and 𝓕^V_t projects onto 𝓕_t by Proposition 1
--   - encoding: components j ∈ {1,…,J}, network layers 1,…,J+1, constraints k ∈ {1,…,K}, periods t ∈ {0,…,T−1} with terminal period T → Fin J, Fin (J+1), Fin K (0-based), periods t : ℕ with decision periods t < T; reason: Lean convention; the paper's index is the Lean index + 1; same instances
--   - reading: standing model assumptions stated in prose: probabilities P(s′ⱼ|sⱼ,aⱼ) ∈ [0,1] (p.6), a policy returns a feasible action a ∈ 𝒜_t(s) at every state (p.6), 𝒮₀ = {s⁰} (p.7) → fields of WDP: P ≥ 0 and Σ_{s′} P = 1 for feasible component actions, 𝒜_t(s) ≠ ∅ for t < T, every initial component state equals s⁰ⱼ; reason: transition probabilities sum to one; the max in (1) needs 𝒜_t(s) ≠ ∅; 𝒮₀ = {s⁰} is assumed on p.7
--   - reading: 𝒜_{t,j}(s) and r_{t,j}(s,a) in the sentence introducing the components (p.6) → A t j sⱼ and r t j sⱼ aⱼ, functions of the component state and action; reason: the display of 𝒜_t(s) and the definition of r_t on the same page use 𝒜_{t,j}(sⱼ) and r_{t,j}(sⱼ,aⱼ); the arguments in the sentence are a notational slip
--   - encoding: finite sets 𝒮_{t,j} and 𝒜_{t,j}(sⱼ), with ℙ, r, C given for t ∈ 𝒯 and 𝒮_{T,j} terminal → S, Act, A, P, r, C indexed by every t : ℕ, Act t j a finite type containing the Finsets A t j s; reason: data at t ≥ T is never read except 𝒮_{T,j}; padding with A t j s = ∅ for t ≥ T meets the stochasticity fields, and finitely many finite action sets lie in a finite type; same instances
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §3.1, Corollary 1, p.12 (PDF 12)

import Mathlib
import Definitions.Def_SelfAdaptingFNR_slackNetwork

open scoped Classical

namespace SelfAdaptingFNR

/-- **Corollary 1 (Slack Network Feasibility)**, Nadarajah & Cire, *Self-Adapting Network
Relaxations for Weakly Coupled MDPs*, SSRN 4081430 (Aug. 2023), §3.1, p.12 (PDF 12): the set of
paths `𝒫_t` of the slack network and the set of feasible state–action pair sequences that satisfy
the linking constraints form a bijection; that is, for every decision period `t ∈ 𝒯` the slack
network `𝒩_t` is a feasibility network of `𝓕_t`. -/
theorem corollary_1 {J K T : ℕ} (M : WDP J K T) (t : ℕ) (ht : t < T) :
    (M.slackNetwork t).IsFeasibilityNetwork := by sorry

end SelfAdaptingFNR
