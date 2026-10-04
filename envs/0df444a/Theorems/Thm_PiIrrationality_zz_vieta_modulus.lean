-- Prove2me | Theorems.Thm_PiIrrationality_zz_vieta_modulus
-- name    : PiIrrationality.zz_vieta_modulus
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:29:32.17608+00:00
-- url     : https://prove2.me/theorems/cef2a544-03ee-4ff6-a100-9ec4c34d1113
-- title:
--   Negative discriminant of the Zeilberger–Zudilin quadratic factor
-- statement:
--   Let
--   $$f(x)=108x^3-2359989x^2+138304x-2048.$$
--   Equation (18) of Zeilberger and Zudilin is the condition $f(N)=0$. The product of the three roots of $f$ is $2048/108=512/27$. The paper records one real root $N_3=21851.691396\ldots$ and a complex-conjugate pair whose common modulus is denoted $|N_1|$.
--
--   Let $N$ be any real number satisfying $21851<N<21852$ and $f(N)=0$. Set
--   $$A=108N-2359989,\qquad B=\frac{2048}{N},$$
--   and write $\Delta$ for the discriminant of the quadratic factor obtained by dividing $f(x)$ by $x-N$:
--   $$\Delta=A^2-432\cdot\frac{2048}{N}.$$
--   The statement asserts that $\Delta<0$, and that the constant term of that quadratic, divided by its leading coefficient, simplifies as
--   $$\frac{2048/N}{108}=\frac{512}{27N}.$$
--
--   Because $\Delta<0$, the other two roots are non-real conjugates. Their product is $512/(27N)$, so this value is $|N_1|^2$ and
--   $$\log|N_1|=\frac12\log\frac{512}{27N}.$$
--   Substituting that identity into the two growth displays after Proposition 2 cancels the explicit factors of $\log 2$ and $\log 3$ in the first display and produces the closed forms $C_0(N)$ and $C_1(N)$ compared with $7.103205334138$ in `PiIrrationality.zz_record_ratio`.
--
--   This is the algebraic step that identifies those closed forms with equation (18). It does not prove the integrality of the linear forms $I_n'$, the evaluation of the integrals, or the irrationality-measure bound $\mu(\pi)\le 7.103205334138$. The two-sided limit required by the transfer lemma is still open; the paper states a limsup for $\log|I_n'|/n$.
-- source:
--   Zeilberger–Zudilin, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, Proposition 2 and equation (18). The product of the three roots of (18) is 2048/108 = 512/27.

import Mathlib.Data.Real.Basic

theorem PiIrrationality.zz_vieta_modulus
    (N : ℝ) (hlo : (21851 : ℝ) < N) (hhi : N < 21852)
    (hroot : 108 * N ^ 3 - 2359989 * N ^ 2 + 138304 * N - 2048 = 0) :
    (108 * N - 2359989) ^ 2 - 432 * (2048 / N) < 0 ∧
      (2048 / N) / 108 = 512 / (27 * N) := by sorry
