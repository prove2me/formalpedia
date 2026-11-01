-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_reverse_quasi_additivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.reverse_quasi_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:11:57.117722+00:00
-- url     : https://prove2.me/theorems/dc8cf88d-c6c4-4bfe-9e63-ffb22745022d
-- title:
--   Remark 7: proved reverse quasi-additivity inequality
-- statement:
--   Let $\tau,\omega$ be finite-dimensional density matrices and $\varepsilon\ge0$ with $2\varepsilon<1$. For retained spectral-subset smoothing, where $\Delta_e$ minimizes the logarithm of cardinality times largest retained eigenvalue at retained mass at least $1-e$,
--
--   $$\Delta_{2\varepsilon}(\tau\otimes\omega)\le\Delta_\varepsilon(\tau)+\Delta_\varepsilon(\omega).$$
--
--   This is the affirmative reverse quasi-additivity inequality. The question-marked inequality in the opposite direction is an open question, not an asserted result.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 5, Remark 7: proved reverse quasi-additivity inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

section SpectralResults

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.5, Remark 7: the affirmative reverse inequality only; the displayed
question-marked lower quasi-additivity conjecture is not asserted. -/
theorem reverse_quasi_additivity (tau : Matrix I I ℂ) (omega : Matrix J J ℂ)
    (htau : IsDensityMatrix tau) (homega : IsDensityMatrix omega)
    (epsilon : ℝ) (hzero : 0 ≤ epsilon) (hone : 2 * epsilon < 1) :
    smoothSpread (Matrix.kronecker tau omega) (2 * epsilon) ≤
    smoothSpread tau epsilon + smoothSpread omega epsilon := by sorry

end SpectralResults

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
