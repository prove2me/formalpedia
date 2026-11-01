-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_spread_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.spread_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:04:56.933387+00:00
-- url     : https://prove2.me/theorems/5b2d3069-d3ba-4074-97d5-48f2033a486a
-- title:
--   §II, eqs.(1),(5): spread nonnegativity, flat-spectrum criterion and additivity
-- statement:
--   Let $\rho$ and $\sigma$ be finite-dimensional density matrices. All logarithms are base two. Write $\Delta(\rho)=\log_2\operatorname{rank}\rho+\log_2\lambda_{\max}(\rho)$, and call a density matrix flat if all its positive eigenvalues are equal. Then
--
--   $$\Delta(\rho)\ge0,\qquad \Delta(\rho)=0\iff\rho\text{ is flat},\qquad \Delta(\rho\otimes\sigma)=\Delta(\rho)+\Delta(\sigma).$$
--
--   A nonflat density has strictly positive spread. Flatness includes rank-one states. These properties measure spectral variation rather than the amount of entanglement.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 2, §II, eqs.(1),(5): spread nonnegativity, flat-spectrum criterion and additivity

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

/-- PDF pp.2--3, (1),(5): nonnegativity, exact flat-support criterion, strict
positivity otherwise, and tensor additivity. -/
theorem spread_properties (rho : Matrix I I ℂ) (sigma : Matrix J J ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    0 ≤ spread rho ∧ (spread rho = 0 ↔ Flat rho) ∧ (¬ Flat rho → 0 < spread rho) ∧
    spread (Matrix.kronecker rho sigma) = spread rho + spread sigma := by sorry

end SpectralResults

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
