-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_minEntropy_le_collision
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.minEntropy_le_collision
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:31:40.100747+00:00
-- url     : https://prove2.me/theorems/625097ef-ccb5-46b5-8077-3b1968dbe57e
-- title:
--   Min entropy is bounded by collision entropy under support inclusion
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $\rho_{AB}$ and $\sigma_B$ be density operators such that $\operatorname{supp}(\operatorname{tr}_A\rho_{AB})\subseteq\operatorname{supp}\sigma_B$. Define
--
--   $$
--   H_2(\rho_{AB}\mid\sigma_B)=-\log_2\operatorname{tr}\!\left[\left((I_A\otimes\sigma_B^{-1/4})\rho_{AB}(I_A\otimes\sigma_B^{-1/4})\right)^2\right].
--   $$
--
--   Negative powers vanish on the kernel and invert positive eigenvalues. Then
--
--   $$
--   H_{\min}(\rho_{AB}\mid\sigma_B)\le H_2(\rho_{AB}\mid\sigma_B).
--   $$
--
--   The support hypothesis is essential for this fixed-reference comparison.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 15, Lemma 3.20

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

/-- Lemma 3.20, PDF p.15, (3.41): fixed reference and the explicit marginal support hypothesis. -/
theorem minEntropy_le_collision {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportIncluded (traceLeft rho) sigma) :
    conditionalMin rho sigma ≤ collisionEntropy rho sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
