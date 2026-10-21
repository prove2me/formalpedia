-- Prove2me | Theorems.Thm_ProConChoice_Rational_lemma_5
-- name    : ProConChoice.Rational.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:38.24304+00:00
-- url     : https://prove2.me/theorems/3d7d5d7b-31f4-4674-8e05-827bb638c27c
-- title:
--   Lemma 5 (Heller–Tompkins), p. 23 — a {0,±1} matrix with ≤ 2 nonzeros per column and a sign-compatible row bipartition is totally unimodular
-- statement:
--   Let $A$ be a real $m \times n$ matrix whose rows are partitioned into two disjoint sets $R_1$ and $R_2$. Then $A$ is **totally unimodular** (every square submatrix has determinant $0$, $1$ or $-1$) if
--
--   1. every entry of $A$ is $0$, $1$ or $-1$;
--   2. every column of $A$ contains at most two nonzero entries;
--   3. if two nonzero entries in a column have the same sign, then the row of one is in $R_1$ and the row of the other is in $R_2$;
--   4. if two nonzero entries in a column have opposite signs, then both rows are in $R_1$ or both are in $R_2$.
--
--   The paper uses this criterion to show that the coefficient matrix of the system (RS)–(CS) is totally unimodular.
--
--   **Formalization Note** Rows and columns are indexed by finite types; $R_1$ is a set of rows and $R_2$ its complement. "Two nonzero entries" refers to two different rows $i \ne i'$; same sign is $a_{ij} a_{i'j} > 0$, opposite signs $a_{ij} a_{i'j} < 0$. Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular`.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 23, Lemma 5 (Heller & Tompkins (1956)); definition of total unimodularity p. 22

import Mathlib

namespace ProConChoice.Rational

/-- Lemma 5 (Heller–Tompkins, p. 23): a matrix whose rows are split into `R₁` and its complement
`R₂` is totally unimodular if (1) every entry is `0`, `1` or `-1`; (2) every column has at most two
nonzero entries; (3) two nonzero entries of a column with the same sign lie in rows of different
parts; (4) two nonzero entries of a column with opposite signs lie in rows of the same part. -/
theorem lemma_5 {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m n ℝ) (R₁ : Set m)
    (h1 : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (h2 : ∀ j, (Finset.univ.filter (fun i => A i j ≠ 0)).card ≤ 2)
    (h3 : ∀ j i i', i ≠ i' → 0 < A i j * A i' j → (i ∈ R₁ ↔ i' ∉ R₁))
    (h4 : ∀ j i i', i ≠ i' → A i j * A i' j < 0 → (i ∈ R₁ ↔ i' ∈ R₁)) :
    A.IsTotallyUnimodular := by sorry

end ProConChoice.Rational
