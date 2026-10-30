-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_constantCharge_code_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.constantCharge_code_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:24:41.948823+00:00
-- url     : https://prove2.me/theorems/7669432d-6a26-40a7-b01a-2923f9aa9052
-- title:
--   §III B3 / Appendix B: constant-charge code bound
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   Fix positive $k,t$ and an integer $\alpha>2$, independent of $n$. There are $C>0$ and $n_0$ such that, for every admissible $n\ge n_0$, every allowed ancillary vector and every erased set of size $t$,
--   $$\mathbb E\epsilon_{\rm Choi}\le Cn^{-1/2},\qquad \mathbb E\epsilon_{\rm worst}\le Cn^{-1/2}.$$
--
--   This records the sufficiently-large-fixed-charge upper bound; it asserts neither a matching lower bound nor exponential concentration.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 8, §III B3 / Appendix B: constant-charge code bound

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

/-- §III B3, PDF p.8: for sufficiently large FIXED charge, the
polynomial partial-decoupling term is dominated. alpha>2 suffices for its
n^(-alpha/4) purified-distance bound; only an O(n^(-1/2)) upper bound is claimed. -/
theorem constantCharge_code_bound (alpha k t : ℕ)
    (ha : 2 < alpha) (hk : 0 < k) (ht : 0 < t)
    (laws : PhysicalUnitaryLaws 2) (hlaw : ∀ n, IsCommutantHaarLaw (U1Group n) (laws n)) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ h : k ≤ n,
    alpha ≤ n-k → t ≤ n →
    ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), ChargeState alpha psi →
    ∀ S : Finset (Fin n), S.card = t →
    (∫ U, choiError (noisyEncoder h (pureDensity psi) S U) ∂laws n) ≤ C / Real.sqrt n ∧
    (∫ U, optimalWorstRecoveryError (noisyEncoder h (pureDensity psi) S U) ∂laws n) ≤ C / Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
