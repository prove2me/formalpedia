-- Prove2me | Theorems.Thm_SelfAdaptingFNR_lemma_EC_2
-- name    : SelfAdaptingFNR.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:26.075618+00:00
-- url     : https://prove2.me/theorems/da232ded-0a99-410a-adb5-0d583ce2b221
-- title:
--   Lemma EC.2: path decomposition of an FNR flow
-- statement:
--   Let a weakly coupled MDP and layered networks $(\mathcal N_t)_{t\in\mathcal T}$ be given, each $\mathcal N_t$ a feasibility network of $\mathscr F_t$, and let $(x',y')$ be any feasible solution of FNR. Fix a period $t\in\mathcal T$ and let $\mathcal P_t$ be the set of paths $((v_j,s_j,a_j,v_{j+1}),\ j\in\mathcal J)$ of $\mathcal N_t$ from layer 1 to layer $J+1$. Then there exists a vector $\alpha\in\mathbb R^{\mathcal P_t}$ such that
--   1. $\alpha_p\in[0,1]$ for all $p\in\mathcal P_t$;
--   2. $\sum_{p\in\mathcal P_t}\alpha_p=1$;
--   3. for every $j\in\mathcal J$ and every arc $(v_j,s_j,a_j,v_{j+1})\in\mathcal E_{t,j}$,
--   $$y'_{t,j}(v_j,s_j,a_j)=\sum_{p\in\mathcal P_t}\alpha_p\,\mathbb 1_{p,j}(v_j,s_j,a_j,v_{j+1}),\tag{EC.16}$$
--   where $\mathbb 1_{p,j}(v_j,s_j,a_j,v_{j+1})$ is one if the arc is the $j$-th arc of $p$ and zero otherwise.
--
--   The flow $y'$ of an FNR solution is thus a convex combination of path flows; this is how the linking constraints, which every path satisfies, pass to FNR.
--
--   Differences from the source:
--   - reading: a feasibility network 𝒩_t with layers 𝒱_{t,1},…,𝒱_{t,J+1}, arcs (vⱼ,sⱼ,aⱼ,vⱼ₊₁), |𝒱_{t,1}| = 1 (p.ec8), 'each node-state-action triple is unique' (p.17) → LayeredNetwork: finite layers, a unique root, arcs as a partial successor map succ j v s a : Option (V j.succ) with feasible labels aⱼ ∈ 𝒜_{t,j}(sⱼ); reason: the FNR variables y_{t,j}(v,sⱼ,aⱼ) are indexed by node–state–action triples, so a triple carries at most one arc
--   - encoding: a feasibility network 𝒩_t for each t ∈ 𝒯 → a family N : ℕ → LayeredNetwork with IsFeasibilityNetwork (N t) for t < T; reason: networks at t ≥ T are never used
--   - reading: ℰ⁻_t(v) with a_{j−1} ∈ 𝒜_{t,j}(s_{j−1}) (p.16) and y_{t,j}(v′,s_{j−1},a_{j−1}) on the right of (19) (p.17) → incoming arcs of component j−1 with a_{j−1} ∈ 𝒜_{t,j−1}(s_{j−1}) and variable y_{t,j−1}; reason: printed typos: the incoming arcs of a layer-j node belong to component j−1
--   - reading: standing model assumptions stated in prose: probabilities P(s′ⱼ|sⱼ,aⱼ) ∈ [0,1] (p.6), a policy returns a feasible action a ∈ 𝒜_t(s) at every state (p.6), 𝒮₀ = {s⁰} (p.7) → fields of WDP: P ≥ 0 and Σ_{s′} P = 1 for feasible component actions, 𝒜_t(s) ≠ ∅ for t < T, every initial component state equals s⁰ⱼ; reason: transition probabilities sum to one; the max in (1) needs 𝒜_t(s) ≠ ∅; 𝒮₀ = {s⁰} is assumed on p.7
--   - encoding: variables x_{t,j}(sⱼ,aⱼ), y_{t,j}(v,sⱼ,aⱼ), x_t(s,a) only for t ∈ 𝒯 and feasible actions → functions of all indices; nonnegativity and all sums restricted to t < T and feasible actions; reason: the other values occur in no constraint and no objective; same programs
--   - encoding: normalization (7) (resp. the DLP constraint at t = 0) → imposed when 0 < T; reason: for T = 0 there are no decision periods and no variables; changes no instance with T ≥ 1
--   - encoding: components j ∈ {1,…,J}, network layers 1,…,J+1, constraints k ∈ {1,…,K}, periods t ∈ {0,…,T−1} with terminal period T → Fin J, Fin (J+1), Fin K (0-based), periods t : ℕ with decision periods t < T; reason: Lean convention; the paper's index is the Lean index + 1; same instances
--   - encoding: indicator 𝟙_{p,j}(vⱼ,sⱼ,aⱼ,vⱼ₊₁) of the edge belonging to p → test that p's j-th node and labels equal (vⱼ,sⱼ,aⱼ); reason: an arc is determined by its node–state–action triple; the arc is p's j-th arc exactly when the triple matches
--   - reading: 𝒜_{t,j}(s) and r_{t,j}(s,a) in the sentence introducing the components (p.6) → A t j sⱼ and r t j sⱼ aⱼ, functions of the component state and action; reason: the display of 𝒜_t(s) and the definition of r_t on the same page use 𝒜_{t,j}(sⱼ) and r_{t,j}(sⱼ,aⱼ); the arguments in the sentence are a notational slip
--   - encoding: finite sets 𝒮_{t,j} and 𝒜_{t,j}(sⱼ), with ℙ, r, C given for t ∈ 𝒯 and 𝒮_{T,j} terminal → S, Act, A, P, r, C indexed by every t : ℕ, Act t j a finite type containing the Finsets A t j s; reason: data at t ≥ T is never read except 𝒮_{T,j}; padding with A t j s = ∅ for t ≥ T meets the stochasticity fields, and finitely many finite action sets lie in a finite type; same instances
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, e-companion EC.4, Lemma EC.2 and (EC.16), p.ec8 (PDF 46)

import Mathlib
import Definitions.Def_SelfAdaptingFNR_FNR

open scoped Classical

namespace SelfAdaptingFNR

/-- **Lemma EC.2**, Nadarajah & Cire, *Self-Adapting Network Relaxations for Weakly Coupled MDPs*,
SSRN 4081430 (Aug. 2023), e-companion EC.4, p.ec8 (PDF 46): for any feasibility network `𝒩_t` of
`𝓕_t` at period `t ∈ 𝒯`, with path set `𝒫_t`, and any feasible solution `(x′, y′)` of FNR, there
is a vector `α ∈ ℝ^{𝒫_t}` with `α_p ∈ [0,1]` for all `p`, `∑_p α_p = 1`, and
`y′_{t,j}(vⱼ,sⱼ,aⱼ) = ∑_{p ∈ 𝒫_t} α_p 𝟙_{p,j}(vⱼ,sⱼ,aⱼ,vⱼ₊₁)` for every `j ∈ 𝒥` and every arc
`(vⱼ,sⱼ,aⱼ,vⱼ₊₁) ∈ ℰ_{t,j}` (EC.16), where `𝟙_{p,j}` indicates that the arc is the `j`-th arc of
`p`.

**Formalization Note.** FNR is posed for a family `N` of networks, one per period; `N t` is a
feasibility network for every decision period. The `j`-th arc of a path `p` is
`(p.node j.castSucc, p.st j, p.act j, p.node j.succ)`; since an arc is determined by its
node–state–action triple, the indicator compares the triple. -/
theorem lemma_EC_2 {J K T : ℕ} (M : WDP J K T) (N : (t : ℕ) → LayeredNetwork M t)
    (hN : ∀ t, t < T → (N t).IsFeasibilityNetwork)
    (x : M.FlowVar) (y : M.ArcVar N) (hxy : M.FNRFeasible N x y) (t : ℕ) (ht : t < T) :
    ∃ α : (N t).Path → ℝ, (∀ p, 0 ≤ α p ∧ α p ≤ 1) ∧ ∑ p, α p = 1 ∧
      ∀ (j : Fin J) (v : (N t).V j.castSucc) (s : M.S t j) (a : M.Act t j)
        (v' : (N t).V j.succ), (N t).succ j v s a = some v' →
        y t j v s a =
          ∑ p : (N t).Path,
            α p * (if p.node j.castSucc = v ∧ p.st j = s ∧ p.act j = a then 1 else 0) := by sorry

end SelfAdaptingFNR
