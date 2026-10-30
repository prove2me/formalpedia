-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_partialTrace_rightMultiply
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.partialTrace_rightMultiply
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:40:28.784557+00:00
-- url     : https://prove2.me/theorems/5b933301-b020-4e8b-b686-b559d887912b
-- title:
--   Partial trace commutes with right multiplication on the retained factor
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. For density operators $\rho_{AB}$ and $\sigma_A$,
--
--   $$
--   \operatorname{tr}_B\!\left[\rho_{AB}(\sigma_A\otimes I_B)\right]
--   =(\operatorname{tr}_B\rho_{AB})\sigma_A.
--   $$
--
--   The partial trace is over the actual second tensor factor, and multiplication by $\sigma_A$ remains on the right.
--
--   This identity transports an operator through a partial trace without reversing multiplication order.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 31, Lemma A.5

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

/-- Lemma A.5, PDF p.31, (A.4): preserve RIGHT multiplication by sigma_A.
The source quantifies normalized densities, though the identity extends further. -/
theorem partialTrace_rightMultiply {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix A A ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    traceRight (rho * Matrix.kronecker sigma (1 : Matrix B B ℂ)) =
      traceRight rho * sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
