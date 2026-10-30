-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_worst
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_worst
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:23:54.593245+00:00
-- url     : https://prove2.me/theorems/1ca5472b-49d7-47f1-b825-04df4f83b71d
-- title:
--   Theorem 3: U(1) worst-case error
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   All logarithms are base two. Asymptotic inequalities are eventual bounds with positive constants chosen before the sizes, ancillary vectors, and erased sets over which they are uniform. For fixed $0<a<1$, $\alpha=an$ is imposed only along an admissible unbounded integer-size subsequence, with positive $k,t$; the threshold may depend on its little-o convergence rate.
--
--   Under $kt^2=o(n)$, there are $C,c>0$ such that eventually, with $B_n=\frac{k\sqrt t}{4n\sqrt{a(1-a)}}(1+Ckt^2/n)$,
--   $$\mathbb E\epsilon_{\rm worst}\le B_n,\qquad\Pr[\epsilon_{\rm worst}>B_n]\le e^{-cn}.$$
--
--   The two conclusions state both mean recovery performance and an exponential upper bound on failure probability.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 7, Theorem 3: U(1) worst-case error

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

/-- Theorem 3, PDF p.7, (55)–(56): leading k*sqrt(t), relative kt²/n. -/
theorem u1_worst (laws : PhysicalUnitaryLaws 2) (h : ∀ n, IsCommutantHaarLaw (U1Group n) (laws n)) :
    U1Performance true laws := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
