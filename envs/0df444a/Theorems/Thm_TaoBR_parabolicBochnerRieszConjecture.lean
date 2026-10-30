-- Prove2me | Theorems.Thm_TaoBR_parabolicBochnerRieszConjecture
-- name    : TaoBR.parabolicBochnerRieszConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:11:36.289814+00:00
-- url     : https://prove2.me/theorems/813defd9-eb50-4256-bec6-7429581f150f
-- title:
--   Conjecture 4.3 — parabolic Bochner–Riesz
-- statement:
--   Write $\mathbf R^n = \mathbf R^{m} \times \mathbf R$ with $n = m + 1$ and $m \ge 1$, and $\xi = (\underline\xi, \xi_n)$. For every smooth compactly supported real-valued $\eta$ on $\mathbf R^n$, every $1 \le p \le \infty$ and every $\delta > \delta(p)$ (computed in dimension $n$), there is $C$ such that every Schwartz $f$ satisfies $\|\tilde S^\delta f\|_p \le C\|f\|_p$. Here $\tilde S^\delta$ is the multiplier with symbol $\eta(\xi)(\xi_n - \frac12|\underline\xi|^2)_+^\delta$.
--
--   This is open for $n \ge 3$; the case $n = 2$ is classical.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 8, Conjecture 4.3 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem parabolicBochnerRieszConjecture (m : ℕ) (hm : 1 ≤ m) :
    ParabolicBochnerRieszConjecture m := by
  sorry

end TaoBR
