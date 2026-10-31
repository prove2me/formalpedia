-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_symplectic_dual_formula
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.symplectic_dual_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:51:04.06677+00:00
-- url     : https://prove2.me/theorems/ac9e8295-cd3c-45ae-988b-739e8773d761
-- title:
--   §VI (55)–(63): symplectic dual lattice and self-dual normal form
-- statement:
--   For $N\ge1$ let $M$ be invertible with integral $A=M\Omega M^T$, and let $L$ be its integer row lattice. Define $L^\perp=\{u:\omega(u,v)\in\mathbb Z\text{ for all }v\in L\}$ and $M^\perp=A^{-1}M$. Then $M^\perp$ generates $L^\perp$ and
--
--   $$M^\perp\Omega M^T=I,\qquad M=A M^\perp,\qquad M^\perp\Omega(M^\perp)^T=(A^{-1})^T.$$
--
--   Moreover $L\subseteq L^\perp$. If $L=L^\perp$, an integral unimodular row change makes its Gram matrix exactly $\Omega$, so the positive normal-form diagonal is the identity.
--
--   The transpose on $A^{-1}$ fixes the source's sign convention.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 8, §VI (55)–(63): symplectic dual lattice and self-dual normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section VI (55)–(63), PDF p.8: dual basis, dual Gram matrix, and self-dual normal form.
The transpose on A inverse is essential. -/
theorem symplectic_dual_formula (N : ℕ) (hN : 0 < N)
    (M : Matrix (Phase N) (Phase N) ℝ)
    (hM : M.det ≠ 0) (hA : IntegralMatrix (latticeGram N M)) :
    rowLattice (dualGenerator N M) = symplecticDual N (rowLattice M) ∧
    dualGenerator N M * sigma N * M.transpose = 1 ∧
    M = latticeGram N M * dualGenerator N M ∧
    latticeGram N (dualGenerator N M) = ((latticeGram N M)⁻¹).transpose ∧
    rowLattice M ⊆ symplecticDual N (rowLattice M) ∧
    (rowLattice M = symplecticDual N (rowLattice M) →
      ∃ R : Matrix (Phase N) (Phase N) ℤ,
        Unimodular R ∧ latticeGram N ((R.map (Int.castRingHom ℝ)) * M) = sigma N) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
