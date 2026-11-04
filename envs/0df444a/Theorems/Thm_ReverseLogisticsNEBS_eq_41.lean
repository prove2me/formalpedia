-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_eq_41
-- name    : ReverseLogisticsNEBS.eq_41
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:49.175736+00:00
-- url     : https://prove2.me/theorems/61000bc8-6586-4e0d-b1b6-e616490fdb7d
-- title:
--   Equation (41) — $\widehat Y^E_j = \bigwedge_{i=j}^N [y_i \vee S^E_i]$ for nested states
-- statement:
--   Let $y_1 \le y_2 \le \dots \le y_N$ be a nested echelon state and $S^E_1, \dots, S^E_N$ any levels. Then the post-expedite echelon positions of the NEBS rule (15) are
--   $$
--   \widehat Y^E_j = \bigwedge_{i=j}^N \big[y_i \vee S^E_i\big] \qquad (j = 1, \dots, N),
--   $$
--   where $\vee$ is the maximum and $\wedge$ the minimum.
--
--   This closed form is the first step of the proof of Theorem 8: it expresses each post-expedite position through the state and the levels of the locations upstream.
--
--   **Formalization Note** Stated for levels in any linear order with a zero (real or extended-real levels alike).
--
--   Differences from the source:
--   - generalization: the levels S^E_it(ω) of an optimal NEBS policy → arbitrary levels in any linearly ordered type with a zero; reason: (41) is a lattice identity of the recursion (15) and uses only that y is nested; the paper's levels are a special case
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), proof of Theorem 8, eq. (41), p.46

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_nebsE

namespace ReverseLogisticsNEBS

/-- **Equation (41)** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, p.46, first step of the proof of
Theorem 8): for a nested echelon state `y_1 ≤ ⋯ ≤ y_N`, the post-expedite echelon positions of the
NEBS rule (15) are `Ŷ^E_j = ⋀_{i=j}^N [y_i ∨ S^E_i]`.

**Formalization Note.** Stated for arbitrary levels in any linear order with a zero (real or
extended-real levels alike); `Finset.inf'` over `{i | j ≤ i}` is `⋀_{i=j}^N`. Nesting
(`Monotone y`) is needed. -/
theorem eq_41 {β : Type*} [LinearOrder β] [Zero β] {N : ℕ} (SE : Fin N → β) (y : Fin N → β)
    (hy : Monotone y) (j : Fin N) :
    nebsE SE y j =
      (Finset.univ.filter (fun i : Fin N => j ≤ i)).inf' ⟨j, by simp⟩
        (fun i => max (y i) (SE i)) := by sorry

end ReverseLogisticsNEBS
