-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_lemma_3_4
-- name    : OverflowBinPacking.IID.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:24.702578+00:00
-- url     : https://prove2.me/theorems/47d702fb-1466-492f-82fd-7a56816be248
-- title:
--   Lemma 3.4, p. 10 — broken-bin probability bounded by opening probability
-- statement:
--   Let the item sizes be independent and nonnegative, $C\ge1$, and $\gamma\ge1$. Suppose each item's probability of exceeding capacity by itself satisfies $\Pr(X_i>1)\le\gamma/C$. For every bin $j$ used by Budgeted Greedy,
--   $$\Pr(\mathrm{BG}\text{ breaks bin }j)\le\frac{\gamma}{C}\Pr(\mathrm{BG}\text{ opens bin }j).$$
--   This per-bin estimate controls the expected overflow penalty through the algorithm's risk budget.
--
--   **Formalization Note** The light-item condition is printed in Lemma 3.4. Bin opening means at least one item is assigned to that bin.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 10, Lemma 3.4

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

namespace OverflowBinPacking.IID

open MeasureTheory

/-- Lemma 3.4, p. 10: a bin's breaking probability is bounded by its
opening probability times the risk budget. -/
theorem lemma_3_4 {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (hLight : ∀ i, (μ i).real (Set.Ioi 1) ≤ γ / C) :
    ∀ j : Fin n,
      (Measure.pi μ).real {x | 1 < usage (bgRule μ C γ) x j n} ≤
        γ / C * (Measure.pi μ).real {x | ∃ i : Fin n, bgRule μ C γ i x = j} := by sorry

end OverflowBinPacking.IID
