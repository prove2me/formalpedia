-- Prove2me | Theorems.Thm_PsdPermanent_permanent_eq_zero_of_diag
-- name    : PsdPermanent.permanent_eq_zero_of_diag
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:30:52.437603+00:00
-- url     : https://prove2.me/theorems/ccaf33b2-795a-4cbe-b48a-a36c76175382
-- title:
--   §3, p.3 — a zero diagonal entry kills the row, the column and $\mathrm{per}(A)$
-- statement:
--   Let $A\succeq0$ be an $n\times n$ Hermitian matrix with $A_{ii}=0$ for some $i$. Then:
--
--   1. $v_i=0$, that is, row $i$ of $V$ vanishes in every factorization $A=VV^\dagger$;
--   2. $|A_{ij}|^2\le A_{ii}A_{jj}$ for all $j$;
--   3. the $i$th row and the $i$th column of $A$ are zero;
--   4. $\mathrm{per}(A)=0$.
--
--   This reduces the sandwich to the case of nonzero rows.
--
--   Differences from the source:
--   - generalization: a Gram factor of full column rank → every factorization A = V V†, with any number of columns; reason: full column rank factors are a special case
--   - encoding: per(A) = ∑_σ ∏_i A_{i,σ(i)} → Mathlib permanent ∑_σ ∏_i A_{σ(i),i}; reason: reindexing by σ⁻¹ gives the same value
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3

import Mathlib
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **Zero diagonal entries.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3: "If A_ii = 0 for some i, then v_i = 0. Equivalently, by Cauchy–Schwarz for the PSD inner
product, |A_ij|² ≤ A_ii A_jj = 0 for all j. Hence the ith row and column of A are zero, and per(A) = 0."

**Formalization Note.** `v_i = 0` is stated for every factorization `A = V * Vᴴ`, with or without full column
rank. Mathlib's `Matrix.permanent` is `∑ σ, ∏ i, A (σ i) i`, the paper's `∑ σ, ∏ i, A i (σ i)` after reindexing
by `σ⁻¹`. -/
theorem permanent_eq_zero_of_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (i : Fin n)
    (hi : A i i = 0) :
    (∀ (d : ℕ) (V : Matrix (Fin n) (Fin d) ℂ), A = V * Vᴴ → V i = 0) ∧
      (∀ j, Complex.normSq (A i j) ≤ (A i i).re * (A j j).re) ∧
      (∀ j, A i j = 0 ∧ A j i = 0) ∧ A.permanent = 0 := by sorry

end PsdPermanent
