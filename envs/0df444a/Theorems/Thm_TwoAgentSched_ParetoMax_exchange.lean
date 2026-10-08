-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoMax_exchange
-- name    : TwoAgentSched.ParetoMax.exchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:23.605233+00:00
-- url     : https://prove2.me/theorems/42bd811e-f2b0-490b-9ce6-dd1204ce818c
-- title:
--   Proof of Theorem 11.3 — between two nondominated pairs, some B-job overtakes some A-job
-- statement:
--   Consider $1\|f^A_{\max}\circ f^B_{\max}$ with nonnegative processing times and nondecreasing cost functions. Let $\sigma$ and $\tilde\sigma$ be nondominated schedules with
--   $$f^A_{\max}(\sigma)<f^A_{\max}(\tilde\sigma)\qquad\text{and}\qquad f^B_{\max}(\tilde\sigma)<f^B_{\max}(\sigma).$$
--   Then some A-job $J^A_h$ and some B-job $J^B_k$ exchange their relative order when switching from $\sigma$ to $\tilde\sigma$: $J^A_h$ precedes $J^B_k$ in $\sigma$, and $J^B_k$ precedes $J^A_h$ in $\tilde\sigma$.
--
--   In the proof of Theorem 11.3 this is the step showing that consecutive nondominated pairs differ by at least one B-job overtaking an A-job; together with Lemma 11.2 it bounds the number of nondominated pairs.
--
--   **Formalization Note** The paper states the claim for the schedules of two consecutive nondominated pairs; it is stated here for any two nondominated schedules with the two strict inequalities, which includes that case. The paper reaches the claim through a B-job $J^B_{k^*}$ attaining $y^B$ in $\sigma$; this statement asserts only the conclusion of that paragraph (some A-job and some B-job exchange order, in the direction the paragraph derives), not that the B-job can be taken to be an arbitrary job attaining $y^B$ — the latter reading fails on small instances.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 240, proof of Theorem 11.3 (the exchanged pair of jobs)

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoMax_Model

namespace TwoAgentSched.ParetoMax

/-- Proof of Theorem 11.3 (p. 240), the exchange claim. If `σ` and `σ̃` are nondominated
schedules with `f^A_max(σ) < f^A_max(σ̃)` and `f^B_max(σ̃) < f^B_max(σ)`, then some A-job
`J^A_h` and some B-job `J^B_k` exchange their relative order when switching from `σ` to `σ̃`:
`J^A_h` precedes `J^B_k` in `σ` and `J^B_k` precedes `J^A_h` in `σ̃`. Processing times are
nonnegative and all costs nondecreasing (regular). -/
theorem exchange {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k))
    (σ σ' : List (TwoAgentSched.MaxMax.Job nA nB))
    (hσ : TwoAgentSched.MaxMax.IsNondominated hA hB p fA fB σ) (hσ' : TwoAgentSched.MaxMax.IsNondominated hA hB p fA fB σ')
    (hAlt : TwoAgentSched.MaxMax.maxCostA hA p fA σ < TwoAgentSched.MaxMax.maxCostA hA p fA σ')
    (hBgt : TwoAgentSched.MaxMax.maxCostB hB p fB σ' < TwoAgentSched.MaxMax.maxCostB hB p fB σ) :
    ∃ (h : Fin nA) (k : Fin nB),
      Precedes σ (Sum.inl h) (Sum.inr k) ∧ Precedes σ' (Sum.inr k) (Sum.inl h) := by sorry

end TwoAgentSched.ParetoMax
