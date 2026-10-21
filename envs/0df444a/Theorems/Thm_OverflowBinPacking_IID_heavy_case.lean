-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_heavy_case
-- name    : OverflowBinPacking.IID.heavy_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:37.060752+00:00
-- url     : https://prove2.me/theorems/a8a7dead-d765-4171-88d8-f02ee333e5f9
-- title:
--   Proof of Theorem 4.4, p. 14 — heavy-item case
-- statement:
--   Let the $n$ item sizes be nonnegative and i.i.d., let $C\ge1$, and put $p=\Pr(X_1>1)$. If $p>\sqrt2/C$, Budgeted Greedy opens a new bin for each item, giving
--   $$\operatorname{cost}(\mathrm{BG})=n(1+Cp).$$
--   Every feasible policy $P$ incurs at least $nCp$ in expected cost:
--   $$nCp\le\operatorname{cost}(P).$$
--   These are the two estimates used for the heavy-item branch of Theorem 4.4.
--
--   **Formalization Note** The comparison is with every admissible policy, the appropriate formulation when an exact optimal policy need not exist.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 14, proof of Theorem 4.4, heavy-item case

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy

namespace OverflowBinPacking.IID

open MeasureTheory

/-- The heavy-item case in the proof of Theorem 4.4, p. 14. -/
theorem heavy_case {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (C : ℝ) (hC : 1 ≤ C)
    (hHeavy : Real.sqrt 2 / C < ν.real (Set.Ioi 1)) :
    cost (fun _ : Fin n => ν) C
      (bgRule (fun _ : Fin n => ν) C (Real.sqrt 2)) =
      (n : ℝ) * (1 + C * ν.real (Set.Ioi 1)) ∧
    ∀ a : Rule n, IsPolicy a →
      (n : ℝ) * C * ν.real (Set.Ioi 1) ≤
        cost (fun _ : Fin n => ν) C a := by sorry

end OverflowBinPacking.IID
