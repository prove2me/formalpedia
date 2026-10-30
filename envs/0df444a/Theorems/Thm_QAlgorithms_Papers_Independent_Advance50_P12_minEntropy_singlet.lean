-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_minEntropy_singlet
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.minEntropy_singlet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:10:58.690193+00:00
-- url     : https://prove2.me/theorems/a1783b6c-8494-4afe-9da7-a99e713cc63b
-- title:
--   Theorem 2 / abstract: min-entropy is maximum achievable singlet fraction
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   Let $\rho_{AB}$ be any bipartite state, let $d_A=\dim H_A$, and let $A'$ be an isomorphic copy of $A$. Write $|\Phi_{AA'}\rangle=d_A^{-1/2}\sum_a|a\rangle|a\rangle$. Define
--   $$q_{\mathrm{corr}}(A|B)_\rho=d_A\max_{\mathcal F:B\to A'}F((\mathrm{id}_A\otimes\mathcal F)(\rho_{AB}),|\Phi\rangle\langle\Phi|)^2,$$
--   where the maximum ranges over all completely positive trace-preserving maps on the full operator algebra. Then
--   $$H_{\min}(A|B)_\rho=-\log_2 q_{\mathrm{corr}}(A|B)_\rho.$$
--   The maximum is attained. This gives the exact operational meaning of conditional min-entropy without any dimension comparison between $A$ and $B$.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 9, Theorem 2 / (32)

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

/-- PDF p.9, Theorem 2 / (32): min-entropy is the negative binary logarithm
of maximal singlet fraction, with an actual maximizing operation. -/
theorem minEntropy_singlet [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    conditionalMinEntropy rho = -elog (qCorr rho) ∧
    ∃ f : Superop B A, IsChannel f ∧
      qCorr rho = (Fintype.card A : ℝ) *
        rootFidelity (idTensorSuperop f rho) (pureDensity (entangledKet A)) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
