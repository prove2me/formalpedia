-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_integerRescaling_lattice
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.integerRescaling_lattice
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:59:25.867729+00:00
-- url     : https://prove2.me/theorems/03cc4d41-1afe-48ff-b388-e1b84f7b1880
-- title:
--   Integer rescaling and dual quotient
-- statement:
--   Let $N\ge1$, let $S$ be a real symplectic $2N\times2N$ matrix, and let $\lambda\ge1$ be an integer. Set $M=\sqrt\lambda S$ and let $L(M)$ be the integer span of its rows. Then
--
--   $$
--   M\Omega M^T=\lambda\Omega,\quad |\det M|=\lambda^N,\quad |L(M)^\perp/L(M)|=\lambda^{2N},\quad \frac{\log_2(\lambda^N)}{N}=\log_2\lambda.
--   $$
--
--   In particular the lattice is symplectically integral and its dual quotient is finite. The number $\lambda^N$ here is the algebraic multiplicity; this result does not construct a normalized physical code space.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 4, §III, (44)–(46): integral rescaling of a self-dual row lattice

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

/-- PDF pp.4–5, (44)–(46), algebraic content only: integral rescaling, determinant,
and actual finite dual quotient. The quotient is not asserted to be a physical code space. -/
theorem integerRescaling_lattice (N : ℕ) (hN : 1 ≤ N) (S : Generator N)
    (hS : IsSymplectic S.transpose) (hdet : S.det ≠ 0) (lambda : ℕ) (hlambda : 1 ≤ lambda) :
    let M : Generator N := Real.sqrt (lambda : ℝ) • S
    SymplecticallyIntegral M ∧
    alternatingGram M = (lambda : ℝ) • sigma N ∧
    |M.det| = (lambda : ℝ) ^ N ∧
    Finite (DualCosets M) ∧ Nat.card (DualCosets M) = lambda ^ (2 * N) ∧
    Real.log ((lambda : ℝ) ^ N) / Real.log 2 / (N : ℝ) =
      Real.log (lambda : ℝ) / Real.log 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
