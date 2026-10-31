-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_integral_symplectic_normal_form
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.integral_symplectic_normal_form
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:50:21.266986+00:00
-- url     : https://prove2.me/theorems/f24c1aea-e9fd-4030-a082-e29a1373a999
-- title:
--   §VI (48)–(54): integral symplectic lattice normal form
-- statement:
--   Let $N\ge1$, let $M$ be an invertible real $2N\times2N$ row generator matrix, and suppose $A=M\Omega M^T$ has integral entries, where $\Omega=\left[\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right]$. There exist an integral matrix $R$ with determinant $\pm1$ and positive integers $d_1,\ldots,d_N$ such that
--
--   $$R A R^T=\begin{pmatrix}0&D\\-D&0\end{pmatrix},\qquad D=\operatorname{diag}(d_1,\ldots,d_N).$$
--
--   Replacing $M$ by $RM$ preserves its integer row lattice. No extra elementary-divisor ordering is required. This is the exact arithmetic normal form used for oscillator lattice codes.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 7, §VI (48)–(54): integral symplectic lattice normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section VI (48)–(54), PDF pp.7–8: integral symplectic lattice normal form.
No elementary-divisor ordering beyond positivity is imposed. -/
theorem integral_symplectic_normal_form (N : ℕ) (hN : 0 < N)
    (M : Matrix (Phase N) (Phase N) ℝ)
    (hM : M.det ≠ 0) (hA : IntegralMatrix (latticeGram N M)) :
    ∃ (R : Matrix (Phase N) (Phase N) ℤ) (d : Fin N → ℤ),
      Unimodular R ∧ (∀ i, 0 < d i) ∧
      rowLattice ((R.map (Int.castRingHom ℝ)) * M) = rowLattice M ∧
      latticeGram N ((R.map (Int.castRingHom ℝ)) * M) =
        Matrix.fromBlocks 0 (Matrix.diagonal (fun i => (d i : ℝ)))
          (-(Matrix.diagonal (fun i => (d i : ℝ)))) 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
