-- Prove2me | Theorems.Thm_SmaleNinth_abs_det_le_factorial_mul_pow
-- name    : SmaleNinth.abs_det_le_factorial_mul_pow
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-06T20:45:11.269162+00:00
-- url     : https://prove2.me/theorems/3b36cdb2-b388-4d1c-a74d-f3a079db8c9a
-- title:
--   Permutation-expansion determinant bound $|\det M| \le r!\,U^r$
-- statement:
--   **Permutation-expansion bound on an integer determinant.**
--
--   Let $M\in\mathbb{Z}^{r\times r}$ have all entries bounded by $U$ in absolute value. Then
--   $$|\det M|\;\le\; r!\,U^{r}.$$
--
--   This is the crude bound that suffices for every size estimate in linear programming: it is weaker than Hadamard's inequality $|\det M|\le r^{r/2}U^{r}$, but its proof needs nothing beyond the Leibniz formula, and only the polynomial bit-size of the right-hand side matters downstream.
--
--   **The argument.** Expand the determinant over permutations,
--   $$\det M=\sum_{\sigma\in S_r}\operatorname{sgn}(\sigma)\prod_{i=1}^{r}M_{\sigma(i),i}.$$
--   The sign is a unit, so each term has absolute value $\prod_i |M_{\sigma(i),i}|\le U^{r}$. There are $r!$ terms, and the triangle inequality gives the bound.
--
--   This statement already exists on the platform in the Mathlib `c5ea003` environment; imports do not cross environments, so it is reproduced here for the default environment, where the rest of the Smale's-Ninth material lives.
-- source:
--   B. Korte, J. Vygen, Combinatorial Optimization: Theory and Algorithms, 6th ed., Springer 2018, Section 4.1 (Size of Vertices and Faces), proof of Theorem 4.4; A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 3.2 (sizes and good characterizations).

import Mathlib

open Matrix Finset

theorem SmaleNinth.abs_det_le_factorial_mul_pow {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (hM : ∀ i j, |M i j| ≤ (U : ℤ)) :
    |M.det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := by sorry
