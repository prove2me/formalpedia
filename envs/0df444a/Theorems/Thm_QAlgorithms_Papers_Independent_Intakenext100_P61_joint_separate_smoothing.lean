-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_joint_separate_smoothing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.joint_separate_smoothing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:08:08.913114+00:00
-- url     : https://prove2.me/theorems/8547b906-5f56-41ff-bc24-d28d4b945c0b
-- title:
--   Equation (9): comparison of joint and separate smoothing
-- statement:
--   Let $\rho$ be a finite density matrix with positive eigenvalues $r_j$, and let $0\le\varepsilon<1$. Over subsets $J$ with $\sum_{j\in J}r_j\ge1-\varepsilon$, define $S_{0,\varepsilon}=\log_2\min|J|$, $S_{\infty,\varepsilon}=-\log_2\min\max_{j\in J}r_j$, and $\Delta_\varepsilon=\log_2\min(|J|\max_{j\in J}r_j)$. Then
--
--   $$\Delta_\varepsilon(\rho)\ge S_{0,\varepsilon}(\rho)-S_{\infty,\varepsilon}(\rho).$$
--
--   At zero error, these three quantities equal $S_0(\rho)$, $S_\infty(\rho)$ and $\Delta(\rho)=S_0-S_\infty$, respectively. Equality can also occur at nonzero error; no converse is claimed. The inequality distinguishes joint from separate spectral optimization.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 3, Equation (9): comparison of joint and separate smoothing

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

/-- PDF p.3, (9): joint versus separate smoothing, and the zero-error identities.
"Generally only" is not strengthened to an iff characterization of equality. -/
theorem joint_separate_smoothing (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon < 1) :
    smoothZero rho epsilon - smoothInfinity rho epsilon ≤ smoothSpread rho epsilon ∧
    smoothZero rho 0 = entropyZero rho ∧ smoothInfinity rho 0 = entropyInfinity rho ∧
    smoothSpread rho 0 = spread rho := by sorry

end SpectralResults

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
