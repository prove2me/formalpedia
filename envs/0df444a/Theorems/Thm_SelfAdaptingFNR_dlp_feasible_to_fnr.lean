-- Prove2me | Theorems.Thm_SelfAdaptingFNR_dlp_feasible_to_fnr
-- name    : SelfAdaptingFNR.dlp_feasible_to_fnr
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:27.185409+00:00
-- url     : https://prove2.me/theorems/9135eb16-f3f7-4111-9442-6a4390250a78
-- title:
--   Proof of Proposition 4, (EC.27)–(EC.37): every DLP solution yields an FNR solution of equal value
-- statement:
--   Let a weakly coupled MDP and feasibility networks $(\mathcal N_t)_{t\in\mathcal T}$ of the sets $\mathscr F_t$ be given. For every feasible solution $x''$ of DLP there exists a feasible solution $(x',y')$ of FNR with the same objective value:
--   $$\sum_{t\in\mathcal T}\sum_{j\in\mathcal J}\sum_{s_j\in\mathcal S_{t,j}}\sum_{a_j\in\mathcal A_{t,j}(s_j)}r_{t,j}(s_j,a_j)\,x'_{t,j}(s_j,a_j)=\sum_{t\in\mathcal T}\sum_{s\in\mathcal S_t}\sum_{a\in\mathcal A_t(s)}r_t(s,a)\,x''_t(s,a).$$
--
--   Together with the optimal value $V_0(s^0)$ of DLP this gives the inequality $z^{\mathrm{FNR}}\ge V_0(s^0)$ of Proposition 4. In the paper, $y'$ puts mass $x''_t(s,a)$ on the path representing $(s,a)$ (EC.27), and $x'$ is then given by (18).
--
--   Differences from the source:
--   - reading: a feasibility network 𝒩_t with layers 𝒱_{t,1},…,𝒱_{t,J+1}, arcs (vⱼ,sⱼ,aⱼ,vⱼ₊₁), |𝒱_{t,1}| = 1 (p.ec8), 'each node-state-action triple is unique' (p.17) → LayeredNetwork: finite layers, a unique root, arcs as a partial successor map succ j v s a : Option (V j.succ) with feasible labels aⱼ ∈ 𝒜_{t,j}(sⱼ); reason: the FNR variables y_{t,j}(v,sⱼ,aⱼ) are indexed by node–state–action triples, so a triple carries at most one arc
--   - encoding: 'each of its paths represents a feasible state–action pair of the WDP and vice versa' (p.3), 'form a bijection' (p.12) → IsFeasibilityNetwork: the map path ↦ its labels ((s₁,a₁),…,(s_J,a_J)) is injective with range 𝓕_t; reason: a bijection between 𝒫_t and 𝓕_t, written as injectivity plus range
--   - encoding: a feasibility network 𝒩_t for each t ∈ 𝒯 → a family N : ℕ → LayeredNetwork with IsFeasibilityNetwork (N t) for t < T; reason: networks at t ≥ T are never used
--   - reading: ℰ⁻_t(v) with a_{j−1} ∈ 𝒜_{t,j}(s_{j−1}) (p.16) and y_{t,j}(v′,s_{j−1},a_{j−1}) on the right of (19) (p.17) → incoming arcs of component j−1 with a_{j−1} ∈ 𝒜_{t,j−1}(s_{j−1}) and variable y_{t,j−1}; reason: printed typos: the incoming arcs of a layer-j node belong to component j−1
--   - reading: DLP flow constraint printed with summation indices s ∈ 𝒮_{t−1}, a ∈ 𝒜_{t−1}(s) and summand in s′, a′ (p.7) → sum over s′ ∈ 𝒮_{t−1}, a′ ∈ 𝒜_{t−1}(s′); reason: printed typo in the bound variables
--   - reading: standing model assumptions stated in prose: probabilities P(s′ⱼ|sⱼ,aⱼ) ∈ [0,1] (p.6), a policy returns a feasible action a ∈ 𝒜_t(s) at every state (p.6), 𝒮₀ = {s⁰} (p.7) → fields of WDP: P ≥ 0 and Σ_{s′} P = 1 for feasible component actions, 𝒜_t(s) ≠ ∅ for t < T, every initial component state equals s⁰ⱼ; reason: transition probabilities sum to one; the max in (1) needs 𝒜_t(s) ≠ ∅; 𝒮₀ = {s⁰} is assumed on p.7
--   - encoding: variables x_{t,j}(sⱼ,aⱼ), y_{t,j}(v,sⱼ,aⱼ), x_t(s,a) only for t ∈ 𝒯 and feasible actions → functions of all indices; nonnegativity and all sums restricted to t < T and feasible actions; reason: the other values occur in no constraint and no objective; same programs
--   - encoding: normalization (7) (resp. the DLP constraint at t = 0) → imposed when 0 < T; reason: for T = 0 there are no decision periods and no variables; changes no instance with T ≥ 1
--   - encoding: components j ∈ {1,…,J}, network layers 1,…,J+1, constraints k ∈ {1,…,K}, periods t ∈ {0,…,T−1} with terminal period T → Fin J, Fin (J+1), Fin K (0-based), periods t : ℕ with decision periods t < T; reason: Lean convention; the paper's index is the Lean index + 1; same instances
--   - reading: 𝒜_{t,j}(s) and r_{t,j}(s,a) in the sentence introducing the components (p.6) → A t j sⱼ and r t j sⱼ aⱼ, functions of the component state and action; reason: the display of 𝒜_t(s) and the definition of r_t on the same page use 𝒜_{t,j}(sⱼ) and r_{t,j}(sⱼ,aⱼ); the arguments in the sentence are a notational slip
--   - encoding: finite sets 𝒮_{t,j} and 𝒜_{t,j}(sⱼ), with ℙ, r, C given for t ∈ 𝒯 and 𝒮_{T,j} terminal → S, Act, A, P, r, C indexed by every t : ℕ, Act t j a finite type containing the Finsets A t j s; reason: data at t ≥ T is never read except 𝒮_{T,j}; padding with A t j s = ∅ for t ≥ T meets the stochasticity fields, and finitely many finite action sets lie in a finite type; same instances
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, e-companion EC.4, proof of Proposition 4, (EC.27)–(EC.37) and the objective identity, pp.ec9–ec11 (PDF 47–49)

import Mathlib
import Definitions.Def_SelfAdaptingFNR_DLP
import Definitions.Def_SelfAdaptingFNR_FNR

open scoped Classical

namespace SelfAdaptingFNR

/-- **Every DLP solution maps to an FNR solution with the same objective value**, proof of
Proposition 4, (EC.27)–(EC.37) and the objective identity, Nadarajah & Cire, *Self-Adapting
Network Relaxations for Weakly Coupled MDPs*, SSRN 4081430 (Aug. 2023), pp.ec9–ec11 (PDF 47–49):
if every `𝒩_t` is a feasibility network of `𝓕_t`, then for every feasible solution `x″` of DLP
there exists a feasible solution `(x′, y′)` of FNR whose objective
`∑_t ∑_j ∑_{sⱼ} ∑_{aⱼ} r_{t,j}(sⱼ,aⱼ) x′_{t,j}(sⱼ,aⱼ)` equals the DLP objective
`∑_t ∑_s ∑_{a ∈ 𝒜_t(s)} r_t(s,a) x″_t(s,a)`.

The paper's construction is `y′_{t,j}(vⱼ,sⱼ,aⱼ) = ∑_{p ∈ 𝒫_t} x″_t((s,a)_p) 𝟙_{p,j}(vⱼ,sⱼ,aⱼ,vⱼ₊₁)`
(EC.27), with `x′` then given by (18). -/
theorem dlp_feasible_to_fnr {J K T : ℕ} (M : WDP J K T)
    (N : (t : ℕ) → LayeredNetwork M t) (hN : ∀ t, t < T → (N t).IsFeasibilityNetwork)
    (x'' : M.DLPVar) (hx'' : M.DLPFeasible x'') :
    ∃ (x : M.FlowVar) (y : M.ArcVar N), M.FNRFeasible N x y ∧
      M.flowObjective x = M.DLPObjective x'' := by sorry

end SelfAdaptingFNR
