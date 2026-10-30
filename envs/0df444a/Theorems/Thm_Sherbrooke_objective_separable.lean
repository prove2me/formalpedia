-- Prove2me | Theorems.Thm_Sherbrooke_objective_separable
-- name    : Sherbrooke.objective_separable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:23:32.786991+00:00
-- url     : https://prove2.me/theorems/e7811fb1-e74e-4ccb-949c-9fec4307600e
-- title:
--   The objective (11) separates by item
-- statement:
--   Let $\iota$ be a finite set of items, $c_i\in\mathbb R$ and $\Xi_i:\mathbb N\to\mathbb R$. Suppose a stock vector $\bar m$ minimizes each item's own term:
--
--   $$
--   c_i\bar m_i+\Xi_i(\bar m_i)\ \le\ c_i k+\Xi_i(k)\qquad\text{for every item } i \text{ and every } k\in\mathbb N .
--   $$
--
--   Then $\bar m$ minimizes the objective (11): $\sum_i[c_i\bar m_i+\Xi_i(\bar m_i)]\le\sum_i[c_im_i+\Xi_i(m_i)]$ for every stock vector $m$.
--
--   This is the first step of the proof of the Appendix Theorem, which reduces (11) to one item at a time.
--
--   Differences from the source:
--
--   - generalization: standing hypotheses on Ξ_i (monotonic decreasing, finite lower bound) and on c_i (nonnegative, not all zero) → hypothesis dropped; reason: separability holds for arbitrary real data; the statement specializes to the source's setting by adding them
--   - reading: we can disregard the summation sign and deal with a single item → a vector whose coordinates minimize their own terms minimizes the sum; reason: this is the implication the proof uses the sentence for
--   - encoding: items i with m_i = 0, 1, 2, … → a Fintype ι and m : ι → ℕ; reason: same instances
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, p. 140 ("Since the objective function in equation (11) is a sum of independent functions for each item i, we can disregard the summation sign and deal with a single item.")

import Mathlib
import Definitions.Def_Sherbrooke_objective

namespace Sherbrooke

/-- **M2: the objective (11) separates by item.** Sherbrooke, *METRIC*, Operations Research 16
(1968), Appendix, proof of the Theorem, p. 140: "Since the objective function in equation (11) is
a sum of independent functions for each item i, we can disregard the summation sign and deal with
a single item."

If each coordinate `m̄ i` minimizes its own term `c_i k + Ξ_i(k)` over `k ∈ ℕ`, then the vector
`m̄` minimizes `objective c Ξ` over all stock vectors `ι → ℕ`.

**Formalization Note.** No hypothesis on `c` or `Ξ` is needed: the statement holds for arbitrary
real data and any finite item type (a generalization of the paper's setting). -/
theorem objective_separable {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ξ : ι → ℕ → ℝ)
    (mbar : ι → ℕ)
    (hmin : ∀ i : ι, ∀ k : ℕ, c i * (mbar i : ℝ) + Ξ i (mbar i) ≤ c i * (k : ℝ) + Ξ i k) :
    ∀ m : ι → ℕ, objective c Ξ mbar ≤ objective c Ξ m := by sorry

end Sherbrooke
