-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_minEntropy_spectral
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.minEntropy_spectral
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:25:44.998892+00:00
-- url     : https://prove2.me/theorems/33f134d3-9650-4481-a576-7314991001ea
-- title:
--   Fixed-reference min entropy: spectral and variational formulas
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $\rho_{AB}$ and the invertible reference $\sigma_B$ be density operators. Put $X=(I_A\otimes\sigma_B^{-1/2})\rho_{AB}(I_A\otimes\sigma_B^{-1/2})$. Then
--
--   $$
--   H_{\min}(\rho_{AB}\mid\sigma_B)=-\log_2\lambda_{\max}(X)=-\log_2\max_{\vartheta_{AB}}\operatorname{tr}(\vartheta_{AB}X),
--   $$
--
--   where the maximum is attained over all normalized density operators $\vartheta_{AB}$.
--
--   This gives both operator and variational expressions for the same fixed-reference entropy.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 10, Lemma 3.5

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

/-- Lemma 3.5, PDF p.10, (3.7): both the spectral formula and its variational maximum.
The reference is an invertible NORMALIZED density, and theta ranges over densities. -/
theorem minEntropy_spectral {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (hinv : IsUnit sigma) :
    conditionalMin rho sigma = -elog (largestEigenvalue (weightedOperator rho sigma (-1 / 2))) ∧
    IsGreatest {r : ℝ | ∃ theta : Matrix (A × B) (A × B) ℂ,
      IsDensityMatrix theta ∧ r = tr (theta * weightedOperator rho sigma (-1 / 2))}
      (largestEigenvalue (weightedOperator rho sigma (-1 / 2))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
