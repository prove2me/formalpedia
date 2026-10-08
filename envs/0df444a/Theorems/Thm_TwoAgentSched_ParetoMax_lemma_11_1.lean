-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoMax_lemma_11_1
-- name    : TwoAgentSched.ParetoMax.lemma_11_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:32.481986+00:00
-- url     : https://prove2.me/theorems/25250c33-22ea-4440-b81a-4be6501dbf66
-- title:
--   Lemma 11.1 — for a fixed A-job and B-job, two nondominated schedules in which the B-job never loses its lead
-- statement:
--   Consider the two-agent single-machine problem $1\|f^A_{\max}\circ f^B_{\max}$ with nonnegative processing times and nondecreasing (regular) cost functions $f^A_h$, $f^B_k$. Let $(y^A,y^B)$ and $(\tilde y^A,\tilde y^B)$ be two nondominated pairs with
--   $$y^A<\tilde y^A\qquad\text{and}\qquad y^B>\tilde y^B .$$
--   Fix an A-job $J^A_h$ and a B-job $J^B_k$. Then there exist a nondominated schedule $\sigma$ corresponding to $(y^A,y^B)$ and a nondominated schedule $\tilde\sigma$ corresponding to $(\tilde y^A,\tilde y^B)$ such that
--   $$J^B_k \text{ precedes } J^A_h \text{ in } \sigma\ \Longrightarrow\ J^B_k \text{ precedes } J^A_h \text{ in } \tilde\sigma .$$
--
--   Moving from the pair with the smaller A-cost to the pair with the smaller B-cost, the lemma says that a fixed B-job never has to fall back behind a fixed A-job it already precedes. It is the one-pair step behind Lemma 11.2.
--
--   **Formalization Note** The schedules $\sigma,\tilde\sigma$ may depend on $h$ and $k$ (quantifiers $\forall h,k\ \exists\sigma,\tilde\sigma$, as printed). "Corresponding to $(y^A,y^B)$" means nondominated with $f^A_{\max}(\sigma)=y^A$ and $f^B_{\max}(\sigma)=y^B$. Nonnegative processing times and regular costs are the paper's standing assumptions (§3); both are used in the moves of the printed proof.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 239, Lemma 11.1

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoMax_Model

namespace TwoAgentSched.ParetoMax

/-- Lemma 11.1 (p. 239). Let `(y^A, y^B)` and `(ỹ^A, ỹ^B)` be nondominated pairs with
`y^A < ỹ^A` and `y^B > ỹ^B`, and fix an A-job `J^A_h` and a B-job `J^B_k`. There are
nondominated schedules `σ` (for `(y^A, y^B)`) and `σ̃` (for `(ỹ^A, ỹ^B)`) such that if `J^B_k`
precedes `J^A_h` in `σ`, then `J^B_k` precedes `J^A_h` in `σ̃`. The schedules may depend on
`h` and `k`. Processing times are nonnegative and all costs nondecreasing (regular). -/
theorem lemma_11_1 {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k))
    (yA yB yA' yB' : ℝ)
    (hy : IsNondominatedPair hA hB p fA fB (yA, yB))
    (hy' : IsNondominatedPair hA hB p fA fB (yA', yB'))
    (hAlt : yA < yA') (hBgt : yB' < yB) (h : Fin nA) (k : Fin nB) :
    ∃ σ σ' : List (TwoAgentSched.MaxMax.Job nA nB),
      IsNondominatedFor hA hB p fA fB (yA, yB) σ ∧
      IsNondominatedFor hA hB p fA fB (yA', yB') σ' ∧
      (Precedes σ (Sum.inr k) (Sum.inl h) → Precedes σ' (Sum.inr k) (Sum.inl h)) := by sorry

end TwoAgentSched.ParetoMax
