-- Prove2me | Theorems.Thm_SmaleNinth_cramer_solution_bound
-- name    : SmaleNinth.cramer_solution_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-06T20:45:10.863107+00:00
-- url     : https://prove2.me/theorems/df35e63b-866a-438b-bf43-9f00dd8b5371
-- title:
--   Cramer bound for a nonsingular integer square system
-- statement:
--   **Cramer's rule turns the determinant bound into a bound on the solution.**
--
--   Let $M\in\mathbb{Z}^{r\times r}$ be nonsingular and $v\in\mathbb{Z}^{r}$, with all entries of both bounded by $U$ in absolute value. If $z\in\mathbb{R}^{r}$ solves $Mz=v$ over the reals, then
--   $$|z_j|\;\le\; r!\,U^{r}\qquad\text{for every }j.$$
--
--   This is the second half of the Cramer--Hadamard size estimate: the first half bounds a determinant, and this one converts that into a bound on the coordinates of the solution of a square nonsingular system. Note the hypothesis is on the *integer* matrix while the solution is sought over $\mathbb{R}$; the point of the statement is exactly that integrality of the data controls the size of a real solution.
--
--   **The argument.** Since $\det M\ne0$ in $\mathbb{Z}$, its image in $\mathbb{R}$ is nonzero and $M$ is invertible over $\mathbb{R}$, so $z$ is the unique real solution. Cramer's identity $M\,(\operatorname{cramer}M\,v)=(\det M)\,v$ together with injectivity of $x\mapsto Mx$ gives
--   $$(\det M)\,z=\operatorname{cramer}M\,v,\qquad\text{that is}\qquad (\det M)\,z_j=\det\big(M\text{ with column }j\text{ replaced by }v\big).$$
--
--   The matrix on the right is again an integer matrix with all entries bounded by $U$, so the companion bound gives $|\det(\cdot)|\le r!\,U^{r}$. The left-hand determinant is a nonzero integer, hence $|\det M|\ge 1$. Dividing yields
--   $$|z_j|\;\le\;|\det M|\,|z_j|\;\le\; r!\,U^{r}.$$
-- source:
--   B. Korte, J. Vygen, Combinatorial Optimization: Theory and Algorithms, 6th ed., Springer 2018, Section 4.1 (Size of Vertices and Faces), proof of Theorem 4.4; A. Schrijver, Theory of Linear and Integer Programming, Wiley 1986, Section 3.2 (sizes and good characterizations).

import Mathlib

open Matrix Finset

theorem SmaleNinth.cramer_solution_bound {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℤ)
    (hM : ∀ i j, |M i j| ≤ (U : ℤ)) (hv : ∀ i, |v i| ≤ (U : ℤ))
    (hdet : M.det ≠ 0)
    (z : Fin r → ℝ)
    (hz : (M.map (Int.cast : ℤ → ℝ)).mulVec z = fun i => ((v i : ℤ) : ℝ)) :
    ∀ j, |z j| ≤ (r.factorial : ℝ) * (U : ℝ) ^ r := by sorry
