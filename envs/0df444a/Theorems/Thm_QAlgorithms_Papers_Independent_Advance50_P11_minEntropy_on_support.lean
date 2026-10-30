-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_minEntropy_on_support
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.minEntropy_on_support
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:42:36.952362+00:00
-- url     : https://prove2.me/theorems/968475b0-a21b-4d48-b791-1294e80048e3
-- title:
--   Spectral formula using the inverse on support
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $\rho_{AB},\sigma_B$ be density operators with $\operatorname{supp}\rho_B\subseteq\operatorname{supp}\sigma_B$, where $\rho_B=\operatorname{tr}_A\rho_{AB}$. If $\Pi_B$ projects onto $\operatorname{supp}\sigma_B$, then
--
--   $$
--   \rho_{AB}=(I_A\otimes\Pi_B)\rho_{AB}(I_A\otimes\Pi_B)^{\dagger}.
--   $$
--
--   Set $X=(I_A\otimes\sigma_B^{-1/2})\rho_{AB}(I_A\otimes\sigma_B^{-1/2})$, with zero action on the kernel. The full spectral/variational formula holds:
--
--   $$
--   H_{\min}(\rho_{AB}\mid\sigma_B)=-\log_2\lambda_{\max}(X)
--   =-\log_2\max_{\vartheta_{AB}}\operatorname{tr}(\vartheta_{AB}X),
--   $$
--
--   where the maximum ranges over normalized density operators and is attained.
--
--   This justifies using a singular actual marginal as a reference without dropping the support condition.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 10, Remark 3.6

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

/-- Remark 3.6, PDF p.10: Lemma 3.5 remains valid with generalized inverses on support.
The marginal support guard is retained, as is the displayed support-compression identity. -/
theorem minEntropy_on_support {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportIncluded (traceLeft rho) sigma) :
    rho = Matrix.kronecker (1 : Matrix A A ℂ) (support sigma) * rho *
      (Matrix.kronecker (1 : Matrix A A ℂ) (support sigma))ᴴ ∧
    conditionalMin rho sigma = -elog (largestEigenvalue (weightedOperator rho sigma (-1 / 2))) ∧
    IsGreatest {r : ℝ | ∃ theta : Matrix (A × B) (A × B) ℂ,
      IsDensityMatrix theta ∧ r = tr (theta * weightedOperator rho sigma (-1 / 2))}
      (largestEigenvalue (weightedOperator rho sigma (-1 / 2))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
