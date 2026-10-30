-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_symmetric_haar_permutation_twirl
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.symmetric_haar_permutation_twirl
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:44:08.197998+00:00
-- url     : https://prove2.me/theorems/5d86ffbe-419d-45c1-a840-d9188da13186
-- title:
--   Lemma 6: symmetric Haar twirl equals permutation twirl
-- statement:
--   Let $d\ge2$, $n\ge1$, and let $M$ be any operator on $(\mathbb C^d)^{\otimes n}$. Let $V$ have normalized Haar law on the actual determinant-one commutant of collective $SU(d)$. For $\pi\in S_n$, let $O_\pi|i_1,\ldots,i_n\rangle=|i_{\pi^{-1}(1)},\ldots,i_{\pi^{-1}(n)}\rangle$. Then
--   $$\mathbb E_VVMV^\dagger=\frac1{n!}\sum_{\pi\in S_n}O_\pi MO_\pi^\dagger.$$
--
--   The operator need not be positive or normalized. Scalar phases repair determinants of permutation matrices and cancel in conjugation; independent special-unitary multiplicity-block sampling is not used.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 21, Lemma 6: symmetric Haar twirl equals permutation twirl

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

/-- Lemma 6, PDF p.21, (D1): arbitrary operator; actual determinant-one
commutant, with projective phases cancelling in conjugation. -/
theorem symmetric_haar_permutation_twirl (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (mu : Measure (Op (CovariantWord d n))) (hmu : IsCommutantHaarLaw (SUGroup d n) mu)
    (M : Op (CovariantWord d n)) :
    (∫ V, V*M*Vᴴ ∂mu) = (n.factorial : ℂ)⁻¹ •
      ∑ pi : Equiv.Perm (Fin n), Schur.tensorPermutation d n pi * M *
        (Schur.tensorPermutation d n pi)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
