-- Prove2me | Theorems.Thm_SelfAdaptingFNR_proposition_1
-- name    : SelfAdaptingFNR.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:40.849755+00:00
-- url     : https://prove2.me/theorems/cb21a12b-a187-4396-8ecd-7058b384948f
-- title:
--   Proposition 1: slack reformulation of $\mathscr F_t$
-- statement:
--   Let a weakly coupled MDP be given, with feasible state–action pairs $\mathscr F_t$ and extended slack set $\mathscr F^V_t$ (slacks $u_{t,k,1}=b_k$, $u_{t,k,j+1}=u_{t,k,j}-C_{t,k,j}(s_j,a_j)$, $u_{t,k,J+1}\ge 0$, component-feasible actions $a\in\times_j\mathcal A_{t,j}(s_j)$). Then for any $t\in\mathcal T$,
--   $$\mathscr F_t=\{(s,a)\mid \exists\,u \text{ such that } (u,s,a)\in\mathscr F^V_t\}.$$
--
--   The linking constraints are thus equivalent to a chain of slack equalities with a nonnegative final slack; this is the basis of the slack network.
--
--   Differences from the source:
--   - generalization: 𝓕^V_t with a ∈ 𝒜_t(s) (the linking constraints already imposed), so that the condition u_{t,k,J+1} ≥ 0 is redundant → 𝓕^V_t with a ∈ ×ⱼ 𝒜_{t,j}(sⱼ), component feasibility only; reason: the printed set is the intersection of this one with {a ∈ 𝒜_t(s)}, so the printed equality follows; this is the content the proof on p.ec5 establishes
--   - reading: '∃v such that (u,s,a) belongs to 𝓕^V_t' → ∃ u; reason: printed typo: u is the bound variable of the set
--   - encoding: components j ∈ {1,…,J}, network layers 1,…,J+1, constraints k ∈ {1,…,K}, periods t ∈ {0,…,T−1} with terminal period T → Fin J, Fin (J+1), Fin K (0-based), periods t : ℕ with decision periods t < T; reason: Lean convention; the paper's index is the Lean index + 1; same instances
--   - reading: standing model assumptions stated in prose: probabilities P(s′ⱼ|sⱼ,aⱼ) ∈ [0,1] (p.6), a policy returns a feasible action a ∈ 𝒜_t(s) at every state (p.6), 𝒮₀ = {s⁰} (p.7) → fields of WDP: P ≥ 0 and Σ_{s′} P = 1 for feasible component actions, 𝒜_t(s) ≠ ∅ for t < T, every initial component state equals s⁰ⱼ; reason: transition probabilities sum to one; the max in (1) needs 𝒜_t(s) ≠ ∅; 𝒮₀ = {s⁰} is assumed on p.7
--   - reading: 𝒜_{t,j}(s) and r_{t,j}(s,a) in the sentence introducing the components (p.6) → A t j sⱼ and r t j sⱼ aⱼ, functions of the component state and action; reason: the display of 𝒜_t(s) and the definition of r_t on the same page use 𝒜_{t,j}(sⱼ) and r_{t,j}(sⱼ,aⱼ); the arguments in the sentence are a notational slip
--   - encoding: finite sets 𝒮_{t,j} and 𝒜_{t,j}(sⱼ), with ℙ, r, C given for t ∈ 𝒯 and 𝒮_{T,j} terminal → S, Act, A, P, r, C indexed by every t : ℕ, Act t j a finite type containing the Finsets A t j s; reason: data at t ≥ T is never read except 𝒮_{T,j}; padding with A t j s = ∅ for t ≥ T meets the stochasticity fields, and finitely many finite action sets lie in a finite type; same instances
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §3.1, Proposition 1 and (11), pp.11–12 (PDF 11–12); proof p.ec5

import Mathlib
import Definitions.Def_SelfAdaptingFNR_slackNetwork

open scoped Classical

namespace SelfAdaptingFNR

/-- **Proposition 1 (Slack reformulation of `𝓕_t`)**, Nadarajah & Cire, *Self-Adapting Network
Relaxations for Weakly Coupled MDPs*, SSRN 4081430 (Aug. 2023), §3.1, pp.11–12 (PDF 11–12):
for any `t ∈ 𝒯`, `𝓕_t = {(s,a) | ∃ u such that (u,s,a) belongs to 𝓕^V_t}`.

**Formalization Note.** `𝓕^V_t` is `WDP.slackSet`, in which `a` ranges over the component action
sets `×ⱼ 𝒜_{t,j}(sⱼ)` rather than the printed `𝒜_t(s)`; with the printed set the statement follows
from this one (generalization). The printed "∃ v" is read as "∃ u", the bound variable of the
set (typo). -/
theorem proposition_1 {J K T : ℕ} (M : WDP J K T) (t : ℕ) (ht : t < T) :
    M.feasiblePairs t = {p | ∃ u : Fin K → Fin (J + 1) → ℝ, (u, p.1, p.2) ∈ M.slackSet t} := by sorry

end SelfAdaptingFNR
