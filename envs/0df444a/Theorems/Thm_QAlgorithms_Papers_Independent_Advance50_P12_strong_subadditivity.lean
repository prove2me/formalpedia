-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_strong_subadditivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.strong_subadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:21:45.026747+00:00
-- url     : https://prove2.me/theorems/62600983-eeb3-4013-8d39-19c12bcdcbed
-- title:
--   §I C, implications / (10) at zero smoothing: strong subadditivity
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   Let $\rho_{ABC}$ be any tripartite state and compute $\rho_{AB}=\operatorname{tr}_C\rho_{ABC}$. Define $q_{\mathrm{corr}}(A|R)$ as $d_A$ times the optimal squared fidelity with a maximally entangled state on $AA'$, after a CPTP map $R\to A'$. Then
--   $$q_{\mathrm{corr}}(A|B)_{\rho_{AB}}\le q_{\mathrm{corr}}(A|BC)_{\rho_{ABC}},\qquad H_{\min}(A|B)_{\rho_{AB}}\ge H_{\min}(A|BC)_{\rho_{ABC}}.$$
--   This is the unsmoothed strong subadditivity consequence actually derived here. The state on $AB$ is its computed marginal, not independent input data.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 6, Section I C, implications / (10) at zero smoothing

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P12

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData cqDensity)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative elog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Support50.P23 (exp2Extended independentProduct)

variable {A B C D X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq X]

/-- PDF p.6, (10) at zero smoothing: discard C by computing the AB marginal;
retain both the correlation inequality and its min-entropy counterpart. -/
theorem strong_subadditivity [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hrho : IsDensityMatrix rho) :
    qCorr (marginalAB rho) ≤ qCorr rho ∧
    conditionalMinEntropy rho ≤ conditionalMinEntropy (marginalAB rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
