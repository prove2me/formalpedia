-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_budgeted_greedy_policy
-- name    : OverflowBinPacking.IID.budgeted_greedy_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:28.211989+00:00
-- url     : https://prove2.me/theorems/d0cd15a5-d939-43c8-a22a-9cc74090b0f0
-- title:
--   §3.1, p. 9 — Budgeted Greedy induces a policy
-- statement:
--   Let $X_1,\ldots,X_n$ be independent nonnegative item sizes, let $C\ge1$, and let $\gamma\ge1$. The deterministic Budgeted Greedy assignment rule is a nonanticipative, measurable, feasible packing policy:
--   $$\operatorname{IsPolicy}(\operatorname{BG}_{\gamma}) .$$
--   In particular, each assignment depends only on earlier realized sizes, and an already overflowed bin is unavailable. This establishes that the algorithm has a well-defined cost in the paper's policy model.
--
--   **Formalization Note** Measurability is made explicit so the expectation defining cost is meaningful. Feasibility is asserted for every outcome vector, as in the shared policy definition.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 9, §3.1, paragraph beginning ‘A deterministic online algorithm induces a policy’

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

namespace OverflowBinPacking.IID

open MeasureTheory

/-- §3.1, p. 9: Algorithm 1 induces a feasible deterministic policy. -/
theorem budgeted_greedy_policy {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ) :
    IsPolicy (bgRule μ C γ) := by sorry

end OverflowBinPacking.IID
