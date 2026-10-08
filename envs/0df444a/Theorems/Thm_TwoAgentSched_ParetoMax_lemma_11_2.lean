-- Prove2me | Theorems.Thm_TwoAgentSched_ParetoMax_lemma_11_2
-- name    : TwoAgentSched.ParetoMax.lemma_11_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:22.136972+00:00
-- url     : https://prove2.me/theorems/55f6c96c-1449-4b77-9ea0-65d6bd32f54a
-- title:
--   Lemma 11.2 — two nondominated schedules in which no B-job loses its lead over any A-job
-- statement:
--   Consider $1\|f^A_{\max}\circ f^B_{\max}$ with nonnegative processing times and nondecreasing cost functions. Let $(y^A,y^B)$ and $(\tilde y^A,\tilde y^B)$ be two nondominated pairs with $y^A<\tilde y^A$ and $y^B>\tilde y^B$. Then there exist a nondominated schedule $\sigma$ corresponding to $(y^A,y^B)$ and a nondominated schedule $\tilde\sigma$ corresponding to $(\tilde y^A,\tilde y^B)$ such that, for every A-job $J^A_h$ and every B-job $J^B_k$,
--   $$J^B_k \text{ precedes } J^A_h \text{ in } \sigma\ \Longrightarrow\ J^B_k \text{ precedes } J^A_h \text{ in } \tilde\sigma .$$
--
--   Unlike Lemma 11.1, one pair of schedules works for all job pairs at once. Lemma 11.2 is what makes the count of Theorem 11.3 work: once a B-job overtakes an A-job, it never has to fall back.
--
--   **Formalization Note** Quantifier order as printed: $\exists\sigma,\tilde\sigma\ \forall h,k$. "Corresponding to" means nondominated with the given values of $f^A_{\max}$ and $f^B_{\max}$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 240, Lemma 11.2

import Mathlib
import Definitions.Def_TwoAgentSched_ParetoMax_Model

namespace TwoAgentSched.ParetoMax

/-- Lemma 11.2 (p. 240). Let `(y^A, y^B)` and `(ỹ^A, ỹ^B)` be nondominated pairs with
`y^A < ỹ^A` and `y^B > ỹ^B`. There are nondominated schedules `σ` (for `(y^A, y^B)`) and `σ̃`
(for `(ỹ^A, ỹ^B)`) such that, for every A-job `J^A_h` and every B-job `J^B_k`, if `J^B_k`
precedes `J^A_h` in `σ`, then `J^B_k` precedes `J^A_h` in `σ̃`. One pair of schedules serves
all job pairs. Processing times are nonnegative and all costs nondecreasing (regular). -/
theorem lemma_11_2 {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ)
    (hfA : ∀ h, Monotone (fA h)) (hfB : ∀ k, Monotone (fB k))
    (yA yB yA' yB' : ℝ)
    (hy : IsNondominatedPair hA hB p fA fB (yA, yB))
    (hy' : IsNondominatedPair hA hB p fA fB (yA', yB'))
    (hAlt : yA < yA') (hBgt : yB' < yB) :
    ∃ σ σ' : List (TwoAgentSched.MaxMax.Job nA nB),
      IsNondominatedFor hA hB p fA fB (yA, yB) σ ∧
      IsNondominatedFor hA hB p fA fB (yA', yB') σ' ∧
      ∀ (h : Fin nA) (k : Fin nB),
        Precedes σ (Sum.inr k) (Sum.inl h) → Precedes σ' (Sum.inr k) (Sum.inl h) := by sorry

end TwoAgentSched.ParetoMax
