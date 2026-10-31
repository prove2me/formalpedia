-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_composite_stein_threshold
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.composite_stein_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:35:29.139423+00:00
-- url     : https://prove2.me/theorems/9d3e3b3c-4103-4a37-9e19-de2e427bd7bd
-- title:
--   Corollary 18: Composite Stein threshold and strong converse
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For any block size $n$, let $\widehat\alpha_n(\mu;\rho,\tau)$ be the minimum rejection probability $\operatorname{tr}[(1-Q)\rho_{AB}^{\otimes n}]$ over all joint effects $0\le Q\le1$ satisfying $\sup_{\sigma_{B^n}\in\mathcal S(B^n)}\operatorname{tr}[Q(\tau_A^{\otimes n}\otimes\sigma_{B^n})]\le\mu$. The alternatives include every correlated block state. Limits run through positive integers and $-\log0=+\infty$. Let $\rho_{AB},\tau_A$ be states with $\rho_A\ll\tau_A$, and $I=D(\rho_{AB}\|\tau_A\otimes\rho_B)$. Then
--   $$\sup\{R\in\mathbb R:\widehat\alpha_n(e^{-nR};\rho,\tau)\to0\}=\inf\{R\in\mathbb R:\widehat\alpha_n(e^{-nR};\rho,\tau)\to1\}=I.$$
--   Both extrema are taken in the extended real line and equal the finite quantity $I$. This identifies the composite Stein threshold and strong-converse threshold over all real rates.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 20, Corollary 18: Composite Stein threshold and strong converse

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

/-- arXiv:1408.6894v5, PDF p.20, Corollary 18, (7.1)--(7.2).
Rates range over ALL reals and membership asserts convergence, not a totalized limit.
Extended extrema preserve nonattainment at the threshold. -/
theorem composite_stein_threshold [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) :
    sSup {r : EReal | ∃ R : ℝ, r = (R : EReal) ∧
      Tendsto (fun k : ℕ => exponentialCompositeError rho tau (k+1) R) atTop (𝓝 (0 : ℝ))} = informationOne rho tau ∧
    sInf {r : EReal | ∃ R : ℝ, r = (R : EReal) ∧
      Tendsto (fun k : ℕ => exponentialCompositeError rho tau (k+1) R) atTop (𝓝 (1 : ℝ))} = informationOne rho tau := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
