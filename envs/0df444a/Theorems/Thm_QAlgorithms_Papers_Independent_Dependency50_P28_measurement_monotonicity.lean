-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_measurement_monotonicity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.measurement_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:47:35.404188+00:00
-- url     : https://prove2.me/theorems/fce77438-c985-4ac8-82cf-52319f445098
-- title:
--   Measurement monotonicity of the logarithmic sandwiched trace
-- statement:
--   Let ρ and σ be positive semidefinite operators with supp ρ contained in supp σ. Let M be any finite POVM and let α≥1. Write Fα for the natural logarithm of the raw sandwiched trace and Fαᴹ for its classical measured counterpart, with support-restricted powers and log 0=−∞. Then
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   $$
--   F_\alpha^M(\rho\Vert\sigma)\leq F_\alpha(\rho\Vert\sigma).
--   $$
--
--   This is the measurement data-processing bound used to compare quantum and classical logarithmic traces.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 5, Lemma III.3 (monotonicity under measurements)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.5: Measurement monotonicity of the logarithmic sandwiched trace. Zero rho and alpha=1 are included. The lemma is on PDF p.5, after the definitions on p.4. -/
theorem measurement_monotonicity (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (hsupp : SupportLE rho sigma) (alpha : ℝ) (ha : 1 ≤ alpha) (M : POVM I) :
    measuredF alpha rho sigma M ≤ F alpha rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
