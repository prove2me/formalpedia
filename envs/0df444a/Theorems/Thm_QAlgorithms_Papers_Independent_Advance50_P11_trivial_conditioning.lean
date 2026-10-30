-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_trivial_conditioning
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.trivial_conditioning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:41:40.582754+00:00
-- url     : https://prove2.me/theorems/b29682eb-bda1-403b-8f0a-0e3cbf48dfcf
-- title:
--   Trivial conditioning gives the unconditional entropies
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $B$ be one dimensional and let $\rho_A=\operatorname{tr}_B\rho_{AB}$. Its unique normalized reference is the scalar identity $1_B$. Then
--
--   $$
--   \begin{aligned}
--   H_{\min}(\rho_{AB}\mid1_B)&=H_{\min}(\rho_{AB}\mid B)=H_{\min}(\rho_A),\\
--   H_{\max}(\rho_{AB}\mid1_B)&=H_{\max}(\rho_{AB}\mid B)=H_{\max}(\rho_A).
--   \end{aligned}
--   $$
--
--   The unconditional quantities are $-\log_2\lambda_{\max}(\rho_A)$ and $\log_2\operatorname{rank}\rho_A$.
--
--   This checks both fixed-reference and optimized-reference conventions on the scalar conditioning space.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 10, Remark 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 3.4, PDF p.10: trivial conditioning register, for fixed AND optimized references.
The sole normalized density on Unit is the scalar identity. -/
theorem trivial_conditioning {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (rho : Matrix (A × Unit) (A × Unit) ℂ) (hrho : IsDensityMatrix rho) :
    conditionalMin rho (1 : Matrix Unit Unit ℂ) = hMin (traceRight rho) ∧
    conditionalMax rho (1 : Matrix Unit Unit ℂ) = hMax (traceRight rho) ∧
    optimizedMin rho = hMin (traceRight rho) ∧
    optimizedMax rho = hMax (traceRight rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
