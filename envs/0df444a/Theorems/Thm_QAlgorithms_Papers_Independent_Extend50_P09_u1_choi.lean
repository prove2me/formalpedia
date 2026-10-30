-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_choi
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_choi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:22:24.895665+00:00
-- url     : https://prove2.me/theorems/dcaaa107-e989-4299-aff6-0dd9c8b9255f
-- title:
--   Theorem 2: U(1) Choi error
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   All logarithms are base two. Asymptotic inequalities are eventual bounds with positive constants chosen before the sizes, ancillary vectors, and erased sets over which they are uniform. For fixed $0<a<1$, $\alpha=an$ is imposed only along an admissible unbounded integer-size subsequence, with positive $k,t$; the threshold may depend on its little-o convergence rate.
--
--   Under $k^2t^2=o(n)$, there are $C,c>0$ such that eventually, with $B_n=\frac{\sqrt{tk}}{4n\sqrt{a(1-a)}}(1+Ck^2t^2/n)$,
--   $$\mathbb E\epsilon_{\rm Choi}\le B_n,\qquad\Pr[\epsilon_{\rm Choi}>B_n]\le e^{-cn}.$$
--
--   The two conclusions state both mean recovery performance and an exponential upper bound on failure probability.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 5, Theorem 2: U(1) Choi error

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

/-- Theorem 2, PDF pp.5–6, (30)–(31): expectation AND exponential upper
tail, with denominator 4*n*sqrt(a*(1-a)). -/
theorem u1_choi (laws : PhysicalUnitaryLaws 2) (h : ∀ n, IsCommutantHaarLaw (U1Group n) (laws n)) :
    U1Performance false laws := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
