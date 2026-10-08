-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_marginalValue_le_topRevenue
-- name    : RevenueOrdered.Nesting.marginalValue_le_topRevenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:34.834447+00:00
-- url     : https://prove2.me/theorems/863d1b41-14f3-492c-b9d5-fb1e5f39bc35
-- title:
--   App. B, p. 36 — the marginal value of capacity is at most r_k
-- statement:
--   Consider the revenue-ordered multi-period dynamic program of §5, with choice probabilities $\mathcal P$ satisfying axioms (i)–(iii) and positive revenues $r$ whose largest value is $r_k$. For every $t\ge 0$ periods remaining and every $q\ge 1$ units left,
--   $$
--   \Delta\mathcal J_t(q)=\mathcal J_t(q)-\mathcal J_t(q-1)\le r_k .
--   $$
--
--   The paper asserts this in the proof of Theorem 5.1 without a formal proof: "the most revenue one could obtain from an extra unit of capacity is the revenue of the most expensive product". It is what makes Lemma .1 applicable with $\delta=-\Delta\mathcal J$, since then $\delta+r_k\ge 0$.
--
--   **Formalization Note** The statement assumes only axioms (i)–(iii) (`IsChoiceSystem`), not regularity, since the argument concerns the dynamic program and not the choice model; under the paper's standing regularity assumption this is the paper's claim.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 36, Appendix B, proof of Theorem 5.1 (r_k − ∆𝒥_{t−1}(q) ⩾ 0)

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

namespace RevenueOrdered.Nesting

/-- App. B, p. 36 (asserted in the proof of Theorem 5.1): the marginal value of a unit of
capacity is at most the revenue of the most expensive product, `∆𝒥_t(q) ≤ r_k`, for every
`t ≥ 0` and `q ≥ 1`. Stated under axioms (i)–(iii) only. -/
theorem marginalValue_le_topRevenue {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsChoiceSystem P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (hq : 1 ≤ q) :
    marginalValue P r t q ≤ topRevenue r := by sorry

end RevenueOrdered.Nesting
