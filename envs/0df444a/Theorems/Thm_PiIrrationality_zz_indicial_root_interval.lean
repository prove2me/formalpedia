-- Prove2me | Theorems.Thm_PiIrrationality_zz_indicial_root_interval
-- name    : PiIrrationality.zz_indicial_root_interval
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T04:07:29.754204+00:00
-- url     : https://prove2.me/theorems/0807040d-d321-4f58-832d-8516f4965918
-- title:
--   Isolating interval for the real zero $N_3$
-- statement:
--   Let
--   \[
--   f(N)=108N^3-2359989N^2+138304N-2048
--   \]
--   be the indicial polynomial in equation (18) of Zeilberger–Zudilin, and set
--   \[
--   L=\frac{2185169139621}{10^{8}},\qquad U=\frac{2185169139622}{10^{8}}.
--   \]
--   There is a unique real number \(N\) with \(L<N<U\) and \(f(N)=0\).
--
--   The interval \((L,U)\) has length \(10^{-8}\) and contains the value \(N_3=21851.691396\ldots\) displayed for the real zero of (18). The sign change \(f(L)<0<f(U)\), together with the strict increase of \(f\) on \([21851,21852]\), places that zero inside \((L,U)\). This is the isolating interval for the numerical comparison of the closed forms \(C_0\) and \(C_1\) with \(7.103205334138\).
--
--   **Formalization Note.** Uniqueness is the statement that any two real roots in \((L,U)\) coincide. The divided-difference estimate is the same one used for the coarser interval \((21851,21852)\).
-- source:
--   D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, https://arxiv.org/abs/1912.06345, Proposition 2 and equation (18). The displayed real zero is $N_3=21851.691396\ldots$.

import Mathlib.Data.Real.Basic

theorem PiIrrationality.zz_indicial_root_interval :
    ∃! N : ℝ,
      (2185169139621 : ℝ) / 10 ^ 8 < N ∧ N < (2185169139622 : ℝ) / 10 ^ 8 ∧
        108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048 = 0 := by
  sorry
