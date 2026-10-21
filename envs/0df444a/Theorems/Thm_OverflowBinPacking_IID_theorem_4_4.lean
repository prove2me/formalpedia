-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_theorem_4_4
-- name    : OverflowBinPacking.IID.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:52.994808+00:00
-- url     : https://prove2.me/theorems/823ed63e-01d1-4ff7-a7ea-827cbeb2ca90
-- title:
--   Theorem 4.4, p. 14 — i.i.d. Budgeted Greedy has approximation factor 3 + 2√2
-- statement:
--   Let $X_1,\ldots,X_n$ be nonnegative i.i.d. item sizes and let an overflowed bin incur penalty $C\ge1$. Budgeted Greedy with risk parameter $\gamma=\sqrt2$ is a measurable, feasible online policy. For every measurable feasible adaptive policy $P$,
--   $$\operatorname{cost}(\mathrm{BG}_{\sqrt2})\le(3+2\sqrt2)\operatorname{cost}(P).$$
--   Thus the same factor holds against the infimum of costs of policies that know the horizon $n$, whether or not an optimum is attained.
--
--   **Formalization Note** The i.i.d. joint law is the product of a single probability measure supported on nonnegative reals. The algorithm's policy status is part of the conclusion, ensuring its expected cost is meaningful. Items and bins use zero-based indices.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 14, Theorem 4.4 (= Theorem 1.2, p. 5)

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

namespace OverflowBinPacking.IID

open MeasureTheory

/-- Theorem 4.4, p. 14 (= Theorem 1.2, p. 5). -/
theorem theorem_4_4 (n : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) :
    IsPolicy (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) ∧
    ∀ a : Rule n, IsPolicy a →
      cost (fun _ : Fin n => ν) C
        (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) ≤
      (3 + 2 * Real.sqrt 2) * cost (fun _ : Fin n => ν) C a := by sorry

end OverflowBinPacking.IID
