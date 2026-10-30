-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_pure_minEntropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.pure_minEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:28:27.290727+00:00
-- url     : https://prove2.me/theorems/9004996d-040b-4a50-9c72-84c72670b667
-- title:
--   Pure-state min entropy relative to the actual marginal
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. Let $\rho_{AB}=\lvert\psi\rangle\langle\psi\rvert$ be pure, let $\rho_B=\operatorname{tr}_A\rho_{AB}$, and let $r$ be the Schmidt rank of $\psi$, equivalently the rank of $\rho_B$. Then
--
--   $$
--   H_{\min}(\rho_{AB}\mid\rho_B)=-\log_2r.
--   $$
--
--   Normalization gives $r\ge1$; for a product vector $r=1$ and the value is zero.
--
--   The formula uses the actual marginal rather than optimizing the reference.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 11, Lemma 3.10

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

/-- Lemma 3.10, PDF pp.11--12, (3.15): condition on the ACTUAL B marginal.
The rank of this marginal is exactly the Schmidt rank of the normalized pure vector. -/
theorem pure_minEntropy {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi) :
    conditionalMin (pureDensity psi) (traceLeft (pureDensity psi)) =
      -elog (supportRank (traceLeft (pureDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
