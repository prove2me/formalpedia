-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_maxEntropy_decoupling
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.maxEntropy_decoupling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:13:52.025971+00:00
-- url     : https://prove2.me/theorems/7ca8802a-93a5-4a66-a04c-8d147298111f
-- title:
--   Theorem 3: max-entropy is decoupling accuracy
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   For any bipartite state $\rho_{AB}$, let $\tau_A=I_A/d_A$, where $d_A=\dim H_A$, and define
--   $$q_{\mathrm{decpl}}(A|B)_\rho=d_A\max_{\sigma_B\text{ state}}F(\rho_{AB},\tau_A\otimes\sigma_B)^2.$$
--   Then
--   $$H_{\max}(A|B)_\rho=\log_2q_{\mathrm{decpl}}(A|B)_\rho.$$
--   A normalized maximizing $\sigma_B$ exists. The reference need not be the actual marginal of $\rho_{AB}$, and the dimension-scaled accuracy can exceed one. This relates the independently defined purification-dual entropy to decoupling.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 10, Theorem 3

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

/-- PDF p.10, Theorem 3: purification-dual max-entropy is log decoupling
accuracy; the optimized normalized reference state is attained. -/
theorem maxEntropy_decoupling [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    purificationMaxEntropy rho = elog (qDecpl rho) ∧
    ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
      qDecpl rho = (Fintype.card A : ℝ) *
        rootFidelity rho (Matrix.kronecker (completelyMixedDensity A) sigma) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
