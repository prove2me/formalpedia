-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_integralAlternating_normalForm
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.integralAlternating_normalForm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:58:56.884993+00:00
-- url     : https://prove2.me/theorems/2df8bb5a-8ed3-4d29-81f9-832be9d1cf7f
-- title:
--   Integral alternating normal form
-- statement:
--   Let $N\ge1$, let $M$ be a nonsingular real $2N\times2N$ row-generator matrix, and suppose $A=M\Omega M^T$ has integer entries, where $\Omega=\begin{pmatrix}0&I\\-I&0\end{pmatrix}$. There are an integer matrix $R$ with $\det R=\pm1$ and positive integers $d_1,\ldots,d_N$ such that, writing $D=\operatorname{diag}(d_1,\ldots,d_N)$ and $B=RAR^T$,
--
--   $$
--   B=\begin{pmatrix}0&D\\-D&0\end{pmatrix},\qquad (B^{-1})^T=\begin{pmatrix}0&D^{-1}\\-D^{-1}&0\end{pmatrix}.
--   $$
--
--   This describes an integral change of lattice basis. No ordering or divisibility condition on the diagonal is asserted.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 4, §III, (34)–(37): integral alternating normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P08

namespace QAlgorithms.Papers.Independent.Intakenext100.P08

open MeasureTheory ProbabilityTheory Matrix

open scoped BigOperators ENNReal

-- Accepted grouped index and source-sign matrix; no paper-local copies.

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
-- The accepted predicate uses column bases and -sigma: apply it to S.transpose.

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
-- The accepted pairing has the opposite sign: exchange its two arguments below.

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/-- PDF p.4, (34)–(37): integral unimodular congruence normal form of a nonsingular
alternating integral pairing matrix. The source does not impose a divisibility ordering. -/
theorem integralAlternating_normalForm (N : ℕ) (hN : 1 ≤ N) (M : Generator N)
    (hM : M.det ≠ 0) (hA : (alternatingGram M).det ≠ 0)
    (hIntegral : SymplecticallyIntegral M) :
    ∃ (R : Matrix (Phase N) (Phase N) ℤ) (d : Fin N → ℤ),
      (R.det = 1 ∨ R.det = -1) ∧
      (∀ i, 0 < d i) ∧
      let B : Generator N :=
        (R.map (fun z => (z : ℝ))) * alternatingGram M *
          (R.map (fun z => (z : ℝ))).transpose
      B.det ≠ 0 ∧
      B = Matrix.fromBlocks 0 (Matrix.diagonal fun i => (d i : ℝ))
        (-(Matrix.diagonal fun i => (d i : ℝ))) 0 ∧
      (B⁻¹).transpose = Matrix.fromBlocks 0 (Matrix.diagonal fun i => (d i : ℝ)⁻¹)
        (-(Matrix.diagonal fun i => (d i : ℝ)⁻¹)) 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
