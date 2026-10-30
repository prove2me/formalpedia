-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_fixedCharge_entropy
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.fixedCharge_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:39:56.451279+00:00
-- url     : https://prove2.me/theorems/f630f2fd-b2e8-4fe2-a242-c83ffb9bdca6
-- title:
--   Appendix B1: fixed-charge entropy
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   For finite positive-dimensional registers $P,Q$ and a positive operator $X^{PQ}$, write $H_{\min}(P|Q)_X=\sup\{h:\exists\sigma_Q\ge0,\ \operatorname{Tr}\sigma_Q=1,\ X\le2^{-h}I_P\otimes\sigma_Q\}$. The supremum is extended-real, so $H_{\min}(0)=+\infty$; throughout, $-\log_2 0=+\infty$.
--
--   Fix nonnegative integers $\alpha,k,t$, independent of $n$, and use the constructed Choi $\Lambda$. There exist $C>0$ and $n_0$, depending on those three integers, such that for every $n\ge n_0$ with $n\ge k+\alpha$ and $n\ge t$, uniformly over the ancillary unit vector,
--   $$H_{\min}(A^*|RE)_\Lambda\ge\alpha\log_2 n-C.$$
--
--   This is a fixed-charge polynomial-decoupling estimate; it includes $\alpha=0$ and does not assert an exponential-in-$n$ entropy bound.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 18, Appendix B1: fixed-charge entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix B1, PDF p.18, (B29): fixed alpha,k,t; remainder is
uniform over the ancillary charge eigenvector and independent of n. -/
theorem fixedCharge_entropy (alpha k t : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ hk : k ≤ n, ∀ ht : t ≤ n,
    alpha ≤ n-k → ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), ChargeState alpha psi →
    (((alpha : ℝ)*Real.logb 2 n-C : ℝ) : EReal) ≤ conditionalMinEntropy (choiLambda hk ht psi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
