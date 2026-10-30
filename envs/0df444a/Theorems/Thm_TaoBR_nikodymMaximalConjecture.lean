-- Prove2me | Theorems.Thm_TaoBR_nikodymMaximalConjecture
-- name    : TaoBR.nikodymMaximalConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:13:29.579509+00:00
-- url     : https://prove2.me/theorems/a8390d96-bcb9-4b33-a24f-f0764d070c43
-- title:
--   Conjecture 4.7 — the Nikodym maximal function conjecture: ‖f**_δ‖_p ≲ δ^{1−n/p−α}‖f‖_p, 1 ≤ p ≤ n, α > 0
-- statement:
--   For $n \ge 2$, every $1 \le p \le n$ and every $\alpha > 0$, the estimate $N(p, \alpha)$ holds: there are $C$ and $\delta_0 > 0$ such that for all $0 < \delta < \delta_0$ and every compactly supported real-valued Schwartz function $f$ on $\mathbf R^n$ (the paper's estimates are a priori, for Schwartz functions),
--   $$\|f^{**}_\delta\|_{L^p(\mathbf R^n)} \le C\delta^{1 - n/p - \alpha}\|f\|_p, \qquad f^{**}_\delta(x) = \sup_{T \ni x}\frac{1}{|T|}\int_T f,$$
--   the supremum over all $1 \times \delta$ tubes $T$ containing $x$.
--
--   This is open for $n \ge 3$; the case $n = 2$ is classical.
--
--   *Correction.* As in Conjecture 4.5, the paper prints the exponent $\frac np - 1 - \alpha$, and for $p < n$ that bound is false ([`TaoBR.not_nikodymMaximalConjecture_printed`](https://prove2.me/theorems/a2964169-1028-42ca-9272-4ea427982fe7)). The exponent here is $1 - \frac np - \alpha$, which agrees with the printed one at $p = n$.
--
--   *Formalization note.* The paper introduces the operator as "the Kakeya maximal function $f^*_\delta$ on $\mathbf R^n$" and writes $f^{**}_\delta$ in the estimate. It is the Nikodym maximal function, written $f^{**}_\delta$ in Theorem 4.10 too.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, Conjecture 4.7 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem nikodymMaximalConjecture (n : ℕ) (hn : 2 ≤ n) : NikodymMaximalConjecture n := by
  sorry

end TaoBR
