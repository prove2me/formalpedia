-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_symplecticDual_generator
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.symplecticDual_generator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:58:27.940802+00:00
-- url     : https://prove2.me/theorems/4a356d9f-778d-4a61-bf70-525bdac30757
-- title:
--   Symplectic-dual row generator
-- statement:
--   Let $N\ge1$, let $M$ be a nonsingular real $2N\times2N$ row-generator matrix, and set $\Omega=\begin{pmatrix}0&I\\-I&0\end{pmatrix}$ and $A=M\Omega M^T$. Assume $A$ has integer entries. Write $L(M)$ for the integer span of the rows and $L(M)^\perp$ for all vectors pairing integrally with every lattice vector. The computed generator $M^\perp=A^{-1}M$ satisfies
--
--   $$
--   L(M^\perp)=L(M)^\perp,\qquad M^\perp\Omega M^T=I,\qquad M^\perp\Omega(M^\perp)^T=(A^{-1})^T.
--   $$
--
--   These are algebraic lattice identities, independent of ideal oscillator states. **Formalization Note** Both nonsingular determinants are explicit; nonsingularity of $A$ also follows from that of $M$.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 4, §III, (31)–(33): symplectic-dual generator

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

/-- PDF p.4, (31)–(33): computed symplectic-dual generator and both pairing identities.
All matrix inverses are protected by determinant hypotheses; no ideal quantum states occur. -/
theorem symplecticDual_generator (N : ℕ) (hN : 1 ≤ N) (M : Generator N)
    (hM : M.det ≠ 0) (hA : (alternatingGram M).det ≠ 0)
    (hIntegral : SymplecticallyIntegral M) :
    (rowLattice (dualGenerator M) : Set (EuclideanSpace ℝ (Phase N))) = symplecticDual M ∧
    dualGenerator M * sigma N * M.transpose = 1 ∧
    alternatingGram (dualGenerator M) = ((alternatingGram M)⁻¹).transpose := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
