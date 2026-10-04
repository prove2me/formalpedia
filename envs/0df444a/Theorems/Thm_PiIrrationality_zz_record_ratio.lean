-- Prove2me | Theorems.Thm_PiIrrationality_zz_record_ratio
-- name    : PiIrrationality.zz_record_ratio
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T03:51:13.863143+00:00
-- url     : https://prove2.me/theorems/8a468c9d-bdf9-459c-829e-79ca7d2b9182
-- title:
--   Closed forms behind the Zeilberger–Zudilin record
-- statement:
--   Let \(L = 2185169139621/10^{8}\). For every real number \(N > L\), write
--   \[
--   C_0(N)=\frac12\log N-4+\frac{\pi}{2\sqrt{3}},
--   \qquad
--   C_1(N)=\log N+4-\frac92\log 2+\frac32\log 3-\frac{\pi}{2\sqrt{3}},
--   \]
--   where \(\log\) is the natural logarithm. Then \(C_0(N)>0\), \(C_1(N)>0\), and
--   \[
--   1+\frac{C_1(N)}{C_0(N)}\le 7.103205334138.
--   \]
--
--   In the world-record paragraph of Zeilberger–Zudilin, the normalized integrals satisfy
--   \[
--   \limsup_{n\to\infty}\frac{\log|I_n'|}{n}
--   =\log|N_1|-\frac52\log 2+4-\frac{\pi}{2\sqrt{3}}+\log\frac{3\sqrt{3}}{4}
--   \]
--   and
--   \[
--   \lim_{n\to\infty}\frac{\log b_n}{n}
--   =\log N_3-\frac52\log 2+4-\frac{\pi}{2\sqrt{3}}+\log\frac{3\sqrt{3}}{4}.
--   \]
--   The roots of equation (18), \(108N^3-2359989N^2+138304N-2048=0\), have product \(512/27\). For the real root \(N_3\) this gives \(|N_1|^2=512/(27N_3)\). Substituting that identity makes the first display equal to \(-C_0(N_3)\) and the second equal to \(C_1(N_3)\). The inequality above is the comparison of those closed forms with the constant printed at the end of the paragraph.
--
--   The ratio decreases as \(N\) increases, so the lower endpoint \(L\) is the worst case. Placing the real root of (18) above \(L\) then feeds this comparison to the linear-form transfer. The integral asymptotics themselves are not part of this statement.
--
--   **Formalization Note.** The Lean statement quantifies over every real \(N>L\). The endpoint \(L\) is the left end of an interval of length \(10^{-8}\) containing the decimal \(21851.691396\ldots\) displayed for \(N_3\).
-- source:
--   D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, https://arxiv.org/abs/1912.06345, World record paragraph and equation (18).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds

theorem PiIrrationality.zz_record_ratio (N : ℝ) (hL : (2185169139621 : ℝ) / 10 ^ 8 < N) :
    0 < (1 / 2) * Real.log N - 4 + Real.pi / (2 * Real.sqrt 3) ∧
      0 < Real.log N + 4 - (9 / 2) * Real.log 2 + (3 / 2) * Real.log 3 -
          Real.pi / (2 * Real.sqrt 3) ∧
        1 + (Real.log N + 4 - (9 / 2) * Real.log 2 + (3 / 2) * Real.log 3 -
              Real.pi / (2 * Real.sqrt 3)) /
            ((1 / 2) * Real.log N - 4 + Real.pi / (2 * Real.sqrt 3)) ≤
          7.103205334138 := by
  sorry
