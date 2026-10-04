-- Prove2me | Theorems.Thm_PiIrrationality_zz_indicial_real_root
-- name    : PiIrrationality.zz_indicial_real_root
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T02:07:54.553987+00:00
-- url     : https://prove2.me/theorems/485ceca3-8223-42a5-87e1-4a004e762e16
-- title:
--   Real root of the Zeilberger–Zudilin indicial cubic
-- statement:
--   Let
--   $$
--   f(N)=108N^{3}-2359989N^{2}+138304N-2048.
--   $$
--   This is the indicial polynomial of the constant-coefficient approximation to the recurrence satisfied by the Zeilberger–Zudilin integrals, their equation (18). The polynomial has a unique real root in the open interval $(21851,21852)$:
--   $$
--   \exists!\, N\in(21851,21852)\quad f(N)=0.
--   $$
--   The root is the quantity $N_3=21851.691396\ldots$ used to describe the exponential growth of the coefficient of $\pi$ in those integrals. The proof is the sign change $f(21851)<0<f(21852)$, the intermediate-value theorem, and a positive lower bound for the first divided difference of $f$ on $[21851,21852]$, which makes $f$ strictly increasing there.
--
--   **Formalization Note.** Uniqueness is claimed only inside $(21851,21852)$, which is the interval containing the displayed real zero $N_3$.
-- source:
--   D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, Proposition 2, equation (18).

import Mathlib.Data.Real.Basic

theorem PiIrrationality.zz_indicial_real_root :
    ∃! N : ℝ, 21851 < N ∧ N < 21852 ∧
      108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048 = 0 := by
  sorry
