-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_pure_entropy_duality
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.pure_entropy_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:29:33.578162+00:00
-- url     : https://prove2.me/theorems/8d982c17-d08e-4b5b-9b7b-ec61058cc796
-- title:
--   Asymmetric pure-state min/rank-max duality
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. For a normalized pure state $\psi_{ABR}$, let $\rho_{AR},\rho_{AB},\rho_R$ denote its actual marginals. Then
--
--   $$
--   H_{\min}(\rho_{AR}\mid\rho_R)=-H_{\max}(\rho_{AB}\mid B).
--   $$
--
--   The min side fixes $\rho_R$; the historical rank-max side optimizes over normalized states on $B$.
--
--   This is the historical asymmetric duality used in the exact merging converse.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 12, Proposition 3.11

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

/-- Proposition 3.11, PDF pp.12--13, (3.21): asymmetric historical duality.
The min reference is rho_R; the max reference is optimized over normalized densities. -/
theorem pure_entropy_duality {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    conditionalMin (marginalAR (pureDensity psi)) (traceRight (pureDensity psi)) =
      -optimizedMax (traceLeft (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
