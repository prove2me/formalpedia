-- Prove2me | Theorems.Thm_StrongConv_cNorm_iteratedDeriv_le
-- name    : StrongConv.cNorm_iteratedDeriv_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:36:46.554004+00:00
-- url     : https://prove2.me/theorems/993e5ead-fa63-442c-93c9-ab073414ee9c
-- title:
--   Lemma 4.1 — Markov inequality for higher derivatives
-- statement:
--   For every real polynomial $h$ of degree at most $q$, every $a > 0$ and every $m \ge 0$,
--   $$\sup_{x \in [0,a]} |h^{(m)}(x)| \le \frac{1}{(2m-1)!!}\Big(\frac{2q^2}{a}\Big)^m \sup_{x \in [0,a]} |h(x)|.$$
--   Here $(2m-1)!!$ is the double factorial, taken as $1$ for $m = 0$. The paper states the lemma for $m \in \mathbb N = \{1, 2, \dots\}$; the case $m = 0$ is the trivial inequality $\|h\| \le \|h\|$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 15, Lemma 4.1 (Markov inequality), which applies Borwein, P. and Erdélyi, T., Polynomials and polynomial inequalities, Graduate Texts in Mathematics 161, Springer (1995), p. 256, E.19(d), https://doi.org/10.1007/978-1-4612-0793-1

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem cNorm_iteratedDeriv_le (q m : ℕ) (h : ℝ[X]) (hh : h.natDegree ≤ q) (a : ℝ) (ha : 0 < a) :
    cNorm 0 (iteratedDeriv m (fun x => h.eval x)) 0 a ≤
      1 / ((2 * m - 1).doubleFactorial : ℝ) * (2 * (q : ℝ) ^ 2 / a) ^ m *
        cNorm 0 (fun x => h.eval x) 0 a := by
  sorry

end StrongConv
