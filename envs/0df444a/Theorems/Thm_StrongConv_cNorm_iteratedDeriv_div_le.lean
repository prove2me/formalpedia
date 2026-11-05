-- Prove2me | Theorems.Thm_StrongConv_cNorm_iteratedDeriv_div_le
-- name    : StrongConv.cNorm_iteratedDeriv_div_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:39:13.83563+00:00
-- url     : https://prove2.me/theorems/c639e857-3af4-4c4f-aefd-e0554bfad468
-- title:
--   Lemma 4.3 — rational Markov inequality
-- statement:
--   Let $f, g$ be real polynomials of degree at most $q$, let $a > 0$ and $m \ge 0$, and suppose $g$ has no zero on $[0, a]$. Put $r = f/g$ and $c = \sup_{x, y \in [0,a]} |g(x)/g(y)|$. Then
--   $$\sup_{x\in[0,a]} |r^{(m)}(x)| \le m!\,\Big(\frac{5cq^2}{a}\Big)^m \sup_{x \in [0,a]} |r(x)|.$$
--   The paper's hypothesis $c < \infty$ is stated as "$g$ has no zero on $[0, a]$". For a polynomial these are equivalent: a zero of $g$ in $[0, a]$ makes the ratios unbounded, and without one, $|g|$ is bounded above and away from zero on $[0, a]$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 15–16, Lemma 4.3 (rational Markov)

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem cNorm_iteratedDeriv_div_le (q m : ℕ) (f g : ℝ[X]) (hf : f.natDegree ≤ q)
    (hg : g.natDegree ≤ q) (a : ℝ) (ha : 0 < a) (hg0 : ∀ x ∈ Set.Icc 0 a, g.eval x ≠ 0) :
    cNorm 0 (iteratedDeriv m (fun x => f.eval x / g.eval x)) 0 a ≤
      m.factorial * (5 * sSup {t | ∃ x ∈ Set.Icc 0 a, ∃ y ∈ Set.Icc 0 a, t = |g.eval x / g.eval y|} *
        (q : ℝ) ^ 2 / a) ^ m * cNorm 0 (fun x => f.eval x / g.eval x) 0 a := by
  sorry

end StrongConv
