-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_decoupling_upper
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.decoupling_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:17:33.408688+00:00
-- url     : https://prove2.me/theorems/cea15cf2-39a0-4c0c-a129-7c4a9b933a55
-- title:
--   Lemma 6: upper bound on decoupling accuracy
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   For every bipartite state $\rho_{AB}$, put $\tau_A=I_A/d_A$ and $q_{\mathrm{decpl}}(A|B)_\rho=d_A\max_{\sigma_B\text{ state}}F(\rho_{AB},\tau_A\otimes\sigma_B)^2$. Then
--   $$2^{H_{\max}(A|B)_\rho}\ge q_{\mathrm{decpl}}(A|B)_\rho.$$
--   This is the converse decoupling bound; the source supplies its proof following reference [19]. Purifying ancillas constructed there impose no extra hypothesis on the input. Extended exponentiation preserves both endpoints.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 10, Lemma 6

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

/-- PDF p.10, Lemma 6: converse decoupling bound. The source includes its
proof following [19]; enlarged purifying ancillas are not input assumptions. -/
theorem decoupling_upper [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    ENNReal.ofReal (qDecpl rho) ≤ exp2Extended (purificationMaxEntropy rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
