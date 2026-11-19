-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_uniform_input_size_conversion
-- name    : StudentTeacher976.Adaptivity.uniform_input_size_conversion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:21:45.905901+00:00
-- url     : https://prove2.me/theorems/b18ca013-8910-4a2a-a05c-cd98a301797b
-- title:
--   Uniform polynomial-time conversion to exact round fixed-point lengths
-- statement:
--   Let $g:\mathbb N\to\mathbb N$ be polynomial-time computable on unary lengths and nondecreasing. Suppose that, for some real $\varepsilon>0$,
--
--   $$
--   1\le g(s)\le s^{1-\varepsilon}\qquad(s\ge1).
--   $$
--
--   There are an integer $d\ge0$ and unary polynomial-time functions $p,m:\mathbb N\to\mathbb N$ such that, for every $n\ge0$,
--
--   $$
--   1\le p(n)\le(n+1)^d,\qquad m(n)=n\,p(n),
--   $$
--
--   and, for every positive $n$,
--
--   $$
--   p(n)=g(m(n)).
--   $$
--
--   Thus the raw construction length is exactly the number of blocks times their length, and its round count is exactly the number of blocks. Both functions are uniform; the result is not merely a length-by-length existence statement. No upper restriction on $\varepsilon$ or unboundedness assumption on $g$ is needed. The zero-length output is handled by a total default, without asserting a fixed-point equation there.
--
--   This strengthens the size-conversion existence argument in Appendix A by providing an explicit polynomial search bound, a uniform compiled exhaustive search, and all positive input lengths.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Appendix A, pp.39–40, equations m=n*p(n), p(n)=g(m), h_n(k)=g(n*k)-k. Explicit polynomial-bound and all-positive-length strengthening of that construction.

import Definitions.Def_StudentTeacher976_Adaptivity_InputConversion
set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.uniform_input_size_conversion (g : ℕ → ℕ) (hpoly : PolyTimeLength g) (hg : Monotone g)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ m : ℕ,0 < m → 1 ≤ g m ∧ (g m : ℝ) ≤ (m : ℝ)^(1-ε)) :
    ∃ (d : ℕ) (p m : ℕ → ℕ),PolyTimeLength p ∧ PolyTimeLength m ∧
      (∀ n,1 ≤ p n ∧ p n ≤ (n+1)^d ∧ m n=n*p n) ∧
      ∀ n,0 < n → p n=g (m n) := by sorry
