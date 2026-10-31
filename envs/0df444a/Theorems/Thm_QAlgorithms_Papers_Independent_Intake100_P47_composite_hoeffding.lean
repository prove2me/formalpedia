-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_composite_hoeffding
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.composite_hoeffding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:31:01.839317+00:00
-- url     : https://prove2.me/theorems/67d418b1-4bea-4ebb-9696-db3e4480df6f
-- title:
--   Theorem 12: Generalized composite Hoeffding exponent (seed main result)
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. For any block size $n$, let $\widehat\alpha_n(\mu;\rho,\tau)$ be the minimum rejection probability $\operatorname{tr}[(1-Q)\rho_{AB}^{\otimes n}]$ over all joint effects $0\le Q\le1$ satisfying $\sup_{\sigma_{B^n}\in\mathcal S(B^n)}\operatorname{tr}[Q(\tau_A^{\otimes n}\otimes\sigma_{B^n})]\le\mu$. The alternatives include every correlated block state. Limits run through positive integers and $-\log0=+\infty$. For states $\rho_{AB},\tau_A$ with $\rho_A\ll\tau_A$ and every $R>0$,
--   $$\lim_{n\to\infty}-\frac1n\log\widehat\alpha_n(e^{-nR};\rho,\tau)=\sup_{0<s<1}\frac{1-s}{s}\left[I_s(\rho\|\tau)-R\right].$$
--   This is the generalized composite Hoeffding exponent. All positive rates are retained, including rates where the exponent is zero or infinity.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 13, Theorem 12: Generalized composite Hoeffding exponent (seed main result)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.13, Theorem 12, (5.1), the main operational result.
All R>0 are retained; the limit and supremum are extended-real valued. -/
theorem composite_hoeffding [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun k : ℕ => normalizedErrorExponent (k+1) (exponentialCompositeError rho tau (k+1) R))
      atTop (𝓝 (hoeffdingValue rho tau R)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
