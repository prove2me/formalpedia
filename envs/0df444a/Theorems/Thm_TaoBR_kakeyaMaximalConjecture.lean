-- Prove2me | Theorems.Thm_TaoBR_kakeyaMaximalConjecture
-- name    : TaoBR.kakeyaMaximalConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:12:35.054982+00:00
-- url     : https://prove2.me/theorems/8592fcc0-ef5f-4e69-8d2b-f335f9608732
-- title:
--   Conjecture 4.5 — the Kakeya maximal function conjecture: ‖f*_δ‖_p ≲ δ^{1−n/p−α}‖f‖_p, 1 ≤ p ≤ n, α > 0
-- statement:
--   For $n \ge 2$, every $1 \le p \le n$ and every $\alpha > 0$, the estimate $K(p, \alpha)$ holds: there are $C$ and $\delta_0 > 0$ such that for all $0 < \delta < \delta_0$ and every compactly supported real-valued Schwartz function $f$ on $\mathbf R^n$ (the paper's estimates are a priori, for Schwartz functions),
--   $$\|f^*_\delta\|_{L^p(S^{n-1})} \le C\delta^{1 - n/p - \alpha}\|f\|_p, \qquad f^*_\delta(\omega) = \sup_{T /\!/ \omega}\frac{1}{|T|}\int_T f,$$
--   the supremum over all $1 \times \delta$ tubes $T$ (solid cylinders of length $1$ and radius $\delta$) with axis direction $\omega$.
--
--   This is open for $n \ge 3$. The case $n = 2$ is Córdoba's theorem ([Amer. J. Math. 99 (1977) 1–22](https://doi.org/10.2307/2374006)).
--
--   *Correction.* The paper prints the exponent $\frac np - 1 - \alpha$. For $p < n$ that bound is false ([`TaoBR.not_kakeyaMaximalConjecture_printed`](https://prove2.me/theorems/47c2bf78-a61b-4157-8fce-ca52e70dcea7)): The exponent here is $1 - \frac np - \alpha$, the standard form of the conjecture, which agrees with the printed one at the critical exponent $p = n$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, Conjecture 4.5 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem kakeyaMaximalConjecture (n : ℕ) (hn : 2 ≤ n) : KakeyaMaximalConjecture n := by
  sorry

end TaoBR
