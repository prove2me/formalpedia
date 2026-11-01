-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_no_entanglement_upper_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.no_entanglement_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:38:03.13999+00:00
-- url     : https://prove2.me/theorems/2d18de70-934a-4dc6-adcc-13a7c33a5775
-- title:
--   Section III: no-entanglement upper bound
-- statement:
--   For $D\ge1$ and $0<\varepsilon\le1$, there exists a single one-way remote-preparation protocol for all pure targets in $\mathbb C^D$, with shared Schmidt rank one and a finite message alphabet of size $K$, such that
--
--   $$\log_2K\le\bigl(4+\log_2(1/\varepsilon)\bigr)D,\qquad \operatorname{Tr}(\psi\,\widetilde\rho_\psi)\ge1-\varepsilon\quad\hbox{for every pure }\psi.$$
--
--   Alice knows the target; Bob's CPTP decoders depend only on the announced message. This is the unaffected no-entanglement upper-bound clause of Theorem 8.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 4, Section III: no-entanglement upper bound

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

/-- Section III, second clause of Theorem 8, PDF pp.4–5. No entanglement is used, and
every pure input has squared fidelity at least 1-eps. -/
theorem no_entanglement_upper_bound (D : ℕ) (hD : 0 < D)
    (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    ∃ P : RSPCode (RSPVector (Fin D)) (Fin D), P.S = 1 ∧
      Real.logb 2 P.K ≤ (4 + Real.logb 2 (1 / eps)) * D ∧
      ∀ psi : RSPVector (Fin D),
        1 - eps ≤ (pureDensity psi.val * P.output psi).trace.re := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
