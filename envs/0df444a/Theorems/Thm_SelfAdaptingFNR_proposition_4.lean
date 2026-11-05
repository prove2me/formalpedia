-- Prove2me | Theorems.Thm_SelfAdaptingFNR_proposition_4
-- name    : SelfAdaptingFNR.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:27.999203+00:00
-- url     : https://prove2.me/theorems/c13299aa-7262-47af-80e4-7bb4fa3281cf
-- title:
--   Proposition 4 (Bound Ordering): $z^{\mathrm{LAG}}\ge z^{\mathrm{FNR}}\ge V_0(s^0)$
-- statement:
--   Let a weakly coupled MDP be given: $J$ component MDPs on the periods $\mathcal T=\{0,\dots,T-1\}$ with finite state and action sets, stochastic component transitions, real rewards, $K$ linking constraints $\sum_j C_{t,k,j}(s_j,a_j)\le b_k$ with real coefficients and right-hand sides, initial state space $\{s^0\}$, and $\mathcal A_t(s)\ne\emptyset$ for all decision periods. Let $(\mathcal N_t)_{t\in\mathcal T}$ be any family of feasibility networks, $\mathcal N_t$ of $\mathscr F_t$. Let $z^{\mathrm{LAG}}$ be the optimal value of D-LAG, $z^{\mathrm{FNR}}$ the optimal value of the feasibility network relaxation FNR built on $(\mathcal N_t)$, and $V_0(s^0)$ the value of an optimal policy (Bellman equations (1)). Then
--   $$z^{\mathrm{LAG}}\ \ge\ z^{\mathrm{FNR}}\ \ge\ V_0(s^0).$$
--
--   Every feasibility network relaxation, in particular the one built on the minimal (self-adapting) network, therefore gives an upper bound on the optimal policy value that is at least as tight as the Lagrangian bound.
--
--   Differences from the source:
--   - reading: standing model assumptions stated in prose: probabilities P(s′ⱼ|sⱼ,aⱼ) ∈ [0,1] (p.6), a policy returns a feasible action a ∈ 𝒜_t(s) at every state (p.6), 𝒮₀ = {s⁰} (p.7) → fields of WDP: P ≥ 0 and Σ_{s′} P = 1 for feasible component actions, 𝒜_t(s) ≠ ∅ for t < T, every initial component state equals s⁰ⱼ; reason: transition probabilities sum to one; the max in (1) needs 𝒜_t(s) ≠ ∅; 𝒮₀ = {s⁰} is assumed on p.7
--   - reading: a feasibility network 𝒩_t with layers 𝒱_{t,1},…,𝒱_{t,J+1}, arcs (vⱼ,sⱼ,aⱼ,vⱼ₊₁), |𝒱_{t,1}| = 1 (p.ec8), 'each node-state-action triple is unique' (p.17) → LayeredNetwork: finite layers, a unique root, arcs as a partial successor map succ j v s a : Option (V j.succ) with feasible labels aⱼ ∈ 𝒜_{t,j}(sⱼ); reason: the FNR variables y_{t,j}(v,sⱼ,aⱼ) are indexed by node–state–action triples, so a triple carries at most one arc
--   - encoding: 'each of its paths represents a feasible state–action pair of the WDP and vice versa' (p.3), 'form a bijection' (p.12) → IsFeasibilityNetwork: the map path ↦ its labels ((s₁,a₁),…,(s_J,a_J)) is injective with range 𝓕_t; reason: a bijection between 𝒫_t and 𝓕_t, written as injectivity plus range
--   - encoding: a feasibility network 𝒩_t for each t ∈ 𝒯 → a family N : ℕ → LayeredNetwork with IsFeasibilityNetwork (N t) for t < T; reason: networks at t ≥ T are never used
--   - reading: ℰ⁻_t(v) with a_{j−1} ∈ 𝒜_{t,j}(s_{j−1}) (p.16) and y_{t,j}(v′,s_{j−1},a_{j−1}) on the right of (19) (p.17) → incoming arcs of component j−1 with a_{j−1} ∈ 𝒜_{t,j−1}(s_{j−1}) and variable y_{t,j−1}; reason: printed typos: the incoming arcs of a layer-j node belong to component j−1
--   - encoding: z^LAG, 'the optimal objective values of D-LAG (or LAG)' (p.17) → optimal value of D-LAG (7)–(10); reason: the paper defines z^LAG through D-LAG or its LP dual LAG; D-LAG is used
--   - encoding: V_t(s) := max over policies of the expected reward, 'also represented recursively through the Bellman equations' (1) (p.7) → V defined by the recursion (1) with V_T := 0, the max as Finset.sup' over 𝒜_t(s); reason: the paper states the two coincide; (1) is the form the proofs use
--   - encoding: optimal objective values of D-LAG, FNR, DLP → suprema in EReal of the objective over the feasible set; reason: Lean convention: ⊥ for an empty feasible set, ⊤ if unbounded; equals the LP optimum when it exists
--   - encoding: variables x_{t,j}(sⱼ,aⱼ), y_{t,j}(v,sⱼ,aⱼ), x_t(s,a) only for t ∈ 𝒯 and feasible actions → functions of all indices; nonnegativity and all sums restricted to t < T and feasible actions; reason: the other values occur in no constraint and no objective; same programs
--   - encoding: normalization (7) (resp. the DLP constraint at t = 0) → imposed when 0 < T; reason: for T = 0 there are no decision periods and no variables; changes no instance with T ≥ 1
--   - encoding: components j ∈ {1,…,J}, network layers 1,…,J+1, constraints k ∈ {1,…,K}, periods t ∈ {0,…,T−1} with terminal period T → Fin J, Fin (J+1), Fin K (0-based), periods t : ℕ with decision periods t < T; reason: Lean convention; the paper's index is the Lean index + 1; same instances
--   - reading: 𝒜_{t,j}(s) and r_{t,j}(s,a) in the sentence introducing the components (p.6) → A t j sⱼ and r t j sⱼ aⱼ, functions of the component state and action; reason: the display of 𝒜_t(s) and the definition of r_t on the same page use 𝒜_{t,j}(sⱼ) and r_{t,j}(sⱼ,aⱼ); the arguments in the sentence are a notational slip
--   - encoding: finite sets 𝒮_{t,j} and 𝒜_{t,j}(sⱼ), with ℙ, r, C given for t ∈ 𝒯 and 𝒮_{T,j} terminal → S, Act, A, P, r, C indexed by every t : ℕ, Act t j a finite type containing the Finsets A t j s; reason: data at t ≥ T is never read except 𝒮_{T,j}; padding with A t j s = ∅ for t ≥ T meets the stochasticity fields, and finitely many finite action sets lie in a finite type; same instances
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §4.1, Proposition 4 (Bound Ordering), p.18 (PDF 18); proof pp.ec9–ec11

import Mathlib
import Definitions.Def_SelfAdaptingFNR_valueFunction
import Definitions.Def_SelfAdaptingFNR_FNR

open scoped Classical

namespace SelfAdaptingFNR

/-- **Proposition 4 (Bound Ordering)**, Nadarajah & Cire, *Self-Adapting Network Relaxations for
Weakly Coupled MDPs*, SSRN 4081430 (Aug. 2023), §4.1, p.18 (PDF 18):
`z^LAG ≥ z^FNR ≥ V₀(s⁰)`.

For every weakly coupled MDP and every family `(𝒩_t)_{t ∈ 𝒯}` of feasibility networks of the
sets `𝓕_t`, the optimal value of the feasibility network relaxation FNR lies between the value
`V₀(s⁰)` of an optimal policy and the optimal value `z^LAG` of the Lagrangian flow program D-LAG.

**Formalization Note.** Optimal values are suprema in `EReal`; `z^LAG` is the optimal value of
D-LAG (p.17), `V₀` is defined by the Bellman equations (1). -/
theorem proposition_4 {J K T : ℕ} (M : WDP J K T) (N : (t : ℕ) → LayeredNetwork M t)
    (hN : ∀ t, t < T → (N t).IsFeasibilityNetwork) :
    M.zFNR N ≤ M.zLAG ∧ (M.V 0 M.s0 : EReal) ≤ M.zFNR N := by sorry

end SelfAdaptingFNR
