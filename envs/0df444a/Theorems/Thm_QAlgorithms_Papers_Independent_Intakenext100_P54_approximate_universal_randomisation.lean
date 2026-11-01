-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_approximate_universal_randomisation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.approximate_universal_randomisation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:33:37.803574+00:00
-- url     : https://prove2.me/theorems/bd204e8f-892f-4d0b-989f-747ad837a4cd
-- title:
--   Theorem 2: approximate universal randomisation
-- statement:
--   Let $D\ge1$ and $0<\varepsilon\le1$. There exist a positive integer $K$ and unitaries $U_1,\ldots,U_K$ on $\mathbb C^D$, chosen independently of the input density operator, such that
--
--   $$K\le (10/\varepsilon)^2D\log_2(20D/\varepsilon),\qquad
--   \frac{1-\varepsilon}{D}I\preceq\frac1K\sum_{k=1}^K U_k\rho U_k^*\preceq\frac{1+\varepsilon}{D}I$$
--
--   for every positive semidefinite trace-one operator $\rho$. The inequalities use the positive semidefinite operator order. This is the universal approximate randomisation needed for remote preparation.
--
--   **Formalization Note** The printed unrestricted positive-error domain is corrected to the small-error domain used by the proof; the discrepancy is recorded in HARD.md.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 3, Theorem 2: approximate universal randomisation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Theorem 2, PDF p.3. The printed domain eps > 0 is corrected to 0 < eps ≤ 1,
the regime used in the proof; eps = 20D contradicts the literal printed bound. -/
theorem approximate_universal_randomisation (D : ℕ) (hD : 0 < D)
    (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ (K : ℝ) ≤ randomisingBound D eps ∧
      ∃ U : Fin K → Matrix.unitaryGroup (Fin D) ℂ, Randomising U eps := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
