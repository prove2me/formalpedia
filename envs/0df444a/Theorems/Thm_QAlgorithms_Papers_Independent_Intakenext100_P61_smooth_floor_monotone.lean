-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_smooth_floor_monotone
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.smooth_floor_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:09:01.422997+00:00
-- url     : https://prove2.me/theorems/07393b40-24fd-4e84-90c2-4acb051517ae
-- title:
--   Equations (10)–(11): smooth-spread floor and monotonicity
-- statement:
--   Let $\rho$ be a density matrix and $0\le\varepsilon'<\varepsilon<1$. Define $\Delta_e(\rho)$ as the base-two logarithm of the minimum of $|J|\max_{j\in J}r_j$ over eigenvalue subsets of retained mass at least $1-e$. Then
--
--   $$\Delta_\varepsilon(\rho)\ge\log_2(1-\varepsilon),\qquad \Delta_\varepsilon(\rho)\le\Delta_{\varepsilon'}(\rho).$$
--
--   The retained operators are subnormalized, so the lower floor can be negative. These estimates control the smoothing dependence.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 4, Equations (10)–(11): smooth-spread floor and monotonicity

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

/-- PDF p.4, (10)--(11): the floor is log(1-epsilon), which can be negative. -/
theorem smooth_floor_monotone (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (epsilon epsilonSmall : ℝ) (hsmall : 0 ≤ epsilonSmall)
    (horder : epsilonSmall < epsilon) (hone : epsilon < 1) :
    logTwo (1 - epsilon) ≤ smoothSpread rho epsilon ∧
    smoothSpread rho epsilon ≤ smoothSpread rho epsilonSmall := by sorry

end SpectralResults

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
