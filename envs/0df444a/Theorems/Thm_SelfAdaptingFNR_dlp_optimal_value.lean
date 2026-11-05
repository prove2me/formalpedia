-- Prove2me | Theorems.Thm_SelfAdaptingFNR_dlp_optimal_value
-- name    : SelfAdaptingFNR.dlp_optimal_value
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:39.790341+00:00
-- url     : https://prove2.me/theorems/3cb88305-fcf7-4e2f-ae6f-b530a187c8bb
-- title:
--   §2.1: the optimal value of DLP equals $V_0(s^0)$
-- statement:
--   Let a weakly coupled MDP be given, with value function $V_t$ defined by the Bellman equations (1). The Bellman equations are formulated as the linear program (PLP), $\min V_0(s^0)$ subject to $V_t(s)\ge r_t(s,a)+\sum_{s'}\mathbb P(s'\mid s,a)V_{t+1}(s')$ and $V_T=0$, and (DLP) is its dual. The optimal value of (DLP) is the optimal policy value:
--   $$\max\Big\{\sum_{t\in\mathcal T}\sum_{s\in\mathcal S_t}\sum_{a\in\mathcal A_t(s)}r_t(s,a)\,x_t(s,a)\ :\ x \text{ feasible for DLP}\Big\}=V_0(s^0).$$
--
--   The maximum is attained by a feasible solution of DLP. The proof of Proposition 4 uses this to pass from $V_0(s^0)$ to feasible solutions of DLP.
--
--   Differences from the source:
--   - reading: standing model assumptions stated in prose: probabilities P(s′ⱼ|sⱼ,aⱼ) ∈ [0,1] (p.6), a policy returns a feasible action a ∈ 𝒜_t(s) at every state (p.6), 𝒮₀ = {s⁰} (p.7) → fields of WDP: P ≥ 0 and Σ_{s′} P = 1 for feasible component actions, 𝒜_t(s) ≠ ∅ for t < T, every initial component state equals s⁰ⱼ; reason: transition probabilities sum to one; the max in (1) needs 𝒜_t(s) ≠ ∅; 𝒮₀ = {s⁰} is assumed on p.7
--   - encoding: V_t(s) := max over policies of the expected reward, 'also represented recursively through the Bellman equations' (1) (p.7) → V defined by the recursion (1) with V_T := 0, the max as Finset.sup' over 𝒜_t(s); reason: the paper states the two coincide; (1) is the form the proofs use
--   - reading: DLP flow constraint printed with summation indices s ∈ 𝒮_{t−1}, a ∈ 𝒜_{t−1}(s) and summand in s′, a′ (p.7) → sum over s′ ∈ 𝒮_{t−1}, a′ ∈ 𝒜_{t−1}(s′); reason: printed typo in the bound variables
--   - encoding: variables x_{t,j}(sⱼ,aⱼ), y_{t,j}(v,sⱼ,aⱼ), x_t(s,a) only for t ∈ 𝒯 and feasible actions → functions of all indices; nonnegativity and all sums restricted to t < T and feasible actions; reason: the other values occur in no constraint and no objective; same programs
--   - encoding: normalization (7) (resp. the DLP constraint at t = 0) → imposed when 0 < T; reason: for T = 0 there are no decision periods and no variables; changes no instance with T ≥ 1
--   - encoding: optimal objective values of D-LAG, FNR, DLP → suprema in EReal of the objective over the feasible set; reason: Lean convention: ⊥ for an empty feasible set, ⊤ if unbounded; equals the LP optimum when it exists
--   - reading: 𝒜_{t,j}(s) and r_{t,j}(s,a) in the sentence introducing the components (p.6) → A t j sⱼ and r t j sⱼ aⱼ, functions of the component state and action; reason: the display of 𝒜_t(s) and the definition of r_t on the same page use 𝒜_{t,j}(sⱼ) and r_{t,j}(sⱼ,aⱼ); the arguments in the sentence are a notational slip
--   - encoding: finite sets 𝒮_{t,j} and 𝒜_{t,j}(sⱼ), with ℙ, r, C given for t ∈ 𝒯 and 𝒮_{T,j} terminal → S, Act, A, P, r, C indexed by every t : ℕ, Act t j a finite type containing the Finsets A t j s; reason: data at t ≥ T is never read except 𝒮_{T,j}; padding with A t j s = ∅ for t ≥ T meets the stochasticity fields, and finitely many finite action sets lie in a finite type; same instances
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §2.1, (PLP)–(DLP), p.7 (PDF 7); used in the proof of Proposition 4, p.ec9

import Mathlib
import Definitions.Def_SelfAdaptingFNR_valueFunction
import Definitions.Def_SelfAdaptingFNR_DLP

open scoped Classical

namespace SelfAdaptingFNR

/-- **The optimal value of DLP is `V₀(s⁰)`**, Nadarajah & Cire, *Self-Adapting Network Relaxations
for Weakly Coupled MDPs*, SSRN 4081430 (Aug. 2023), §2.1, (PLP)–(DLP), p.7 (PDF 7); used in the
proof of Proposition 4, p.ec9. The Bellman equations (1) are formulated as the linear program
(PLP), whose optimal value is `V₀(s⁰)`, and (DLP) is its dual; the optimal value of (DLP) is
therefore `V₀(s⁰)`, and the maximum of (DLP) is attained.

**Formalization Note.** `WDP.zDLP` is the supremum in `EReal` of the DLP objective over the DLP
feasible set, and the second clause says that a feasible solution attains it (the paper writes
`max`); `WDP.V` is defined by (1). -/
theorem dlp_optimal_value {J K T : ℕ} (M : WDP J K T) :
    M.zDLP = (M.V 0 M.s0 : EReal) ∧
      ∃ x : M.DLPVar, M.DLPFeasible x ∧ M.DLPObjective x = M.V 0 M.s0 := by sorry

end SelfAdaptingFNR
