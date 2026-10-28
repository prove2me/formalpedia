-- Prove2me | Theorems.Thm_TwoAgentSched_Knapsack_knapsack_encoding_reduction
-- name    : TwoAgentSched.Knapsack.knapsack_encoding_reduction
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:41:22.391959+00:00
-- url     : https://prove2.me/theorems/bef82861-0515-4c24-b867-16f0ecd53b9a
-- title:
--   Theorem 5.2 — Polynomial-Time Binary Encoding Reduction for Two-Agent Weighted Completion and Makespan
-- statement:
--   There exists a polynomial-time computable function $f$ on $\mathrm{BSym}$ strings that maps binary-encoded KNAPSACK instances $\mathrm{knapsackCode}(u, w, b, W)$ to binary-encoded two-agent scheduling instances in $\mathrm{targetLang}$ according to $\mathrm{construction}(u, w)$ and thresholds $Q_A(u, w, W)$, $Q_B(u, w, b)$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, Scheduling problems with two competing agents, Operations Research 52(2), p. 233, Theorem 5.2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TwoAgentSched_Knapsack_Problem51
import Definitions.Def_TwoAgentSched_Knapsack_Construction

namespace TwoAgentSched.Knapsack

open CookPvsNP ProjSchedTW.Complexity

/-- Polynomial-time binary encoding reduction for Theorem 5.2 (Agnetis et al. 2004, p. 233):
there is a polynomial-time computable function `f` on `BSym` strings that maps binary-encoded
KNAPSACK instances `knapsackCode u w b W` to binary-encoded two-agent scheduling instances in
`targetLang` according to `construction u w` and thresholds `QA u w W`, `QB u w b`. -/
theorem knapsack_encoding_reduction :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ x : List BSym,
        ((∃ (n : ℕ) (u w : Fin n → ℕ) (b W : ℤ),
            0 < ∑ i, w i * u i ∧
            (construction u w).RecYes ((QA u w W : ℤ) : ℝ) ((QB u w b : ℤ) : ℝ) ∧
            x = knapsackCode u w b W) ∨
          (∃ (n : ℕ) (u w : Fin n → ℕ) (b W : ℤ),
            ∑ i, w i * u i = 0 ∧ KnapsackYes u w b W ∧ x = knapsackCode u w b W)) ↔
          f x ∈ targetLang := by sorry

end TwoAgentSched.Knapsack
