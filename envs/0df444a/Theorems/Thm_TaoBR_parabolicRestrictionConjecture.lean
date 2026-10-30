-- Prove2me | Theorems.Thm_TaoBR_parabolicRestrictionConjecture
-- name    : TaoBR.parabolicRestrictionConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:12:10.751752+00:00
-- url     : https://prove2.me/theorems/19b619af-2b60-47ad-ab10-70b49d19141c
-- title:
--   Conjecture 4.4 — parabolic restriction, for 1 ≤ p < 2n/(n+1)
-- statement:
--   Write $\mathbf R^n = \mathbf R^{m} \times \mathbf R$ with $n = m + 1$ and $m \ge 1$, and let $S = \{(\underline\xi, \frac12|\underline\xi|^2) : |\underline\xi| \le 1\}$. For every $1 \le p < 2n/(n+1)$ there is $C$ such that every Schwartz $f$ on $\mathbf R^n$ satisfies
--   $$\Big(\int_{|\underline\xi| \le 1}\big|\hat f(\underline\xi, \tfrac12|\underline\xi|^2)\big|^p\,d\underline\xi\Big)^{1/p} \le C\|f\|_p.$$
--
--   This is open for $n \ge 3$; the case $n = 2$ is classical.
--
--   *Formalization note.* $L^p(S)$ is taken with the measure $d\underline\xi$ of the parametrization of $S$ by its projection to $\mathbf R^m$, which has bounded density with respect to surface measure on $S$ and vice versa. The paper's $|\underline\xi| \lesssim 1$ is taken with the constant $1$.
--
--   *Correction.* The paper prints the range $1 \le p < 2n/(n-1)$. The critical exponent of the paraboloid, like the sphere's, is $2n/(n+1)$; p. 1 gives this index for the sphere, and p. 10 uses it for the paraboloid ("the restriction theorem at the critical index $p = 2n/(n+1)$ is invariant under parabolic scaling"). With the printed range the conjecture is false ([`TaoBR.not_parabolicRestriction_printed`](https://prove2.me/theorems/517d7ce2-e6a8-4a1a-83a7-c900c57c57bb)).
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 8, Conjecture 4.4 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem parabolicRestrictionConjecture (m : ℕ) (hm : 1 ≤ m) :
    ParabolicRestrictionConjecture m := by
  sorry

end TaoBR
