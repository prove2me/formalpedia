-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_cayley_logarithmic
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.cayley_logarithmic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:28:50.135994+00:00
-- url     : https://prove2.me/theorems/265864fb-83b0-4782-8460-f4c37791de6e
-- title:
--   Section 3 Application 4: Cayley powers and their B norms
-- statement:
--   For $V(z)=(z-1)/(z+1)$, its scalar Besov norms satisfy
--
--   $$\|V^n\|_{\mathcal B}\asymp\log n\qquad(n\to\infty).$$
--
--   If $-A$ generates a bounded C0-semigroup on a Hilbert space, then $\|V(A)^n\|\le C_A\|V^n\|_{\mathcal B}$ for every $n\ge0$, and consequently $\|V(A)^n\|=O(\log n)$. The source leaves optimality of the operator bound open; no operator lower bound or power boundedness is asserted.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 16, Section 3 Application 4: Cayley powers and their B norms

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Section 3 Application 4: Cayley powers and their B norms, arXiv:2202.03143v1, PDF page(s) 16. -/
theorem cayley_logarithmic
:
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal (c * Real.log n) ≤ bSize (fun z => scalarCayley z ^ n) ∧
      bSize (fun z => scalarCayley z ^ n) ≤ ENNReal.ofReal (C * Real.log n)) ∧
    (∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
      ∀ A : DenseClosedGraphOperator X, HilbertGenerator A →
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
        ENNReal.ofReal ‖operatorCayley A ^ n‖ ≤
          ENNReal.ofReal C * bSize (fun z => scalarCayley z ^ n)) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        ‖operatorCayley A ^ n‖ ≤ C * Real.log n)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
