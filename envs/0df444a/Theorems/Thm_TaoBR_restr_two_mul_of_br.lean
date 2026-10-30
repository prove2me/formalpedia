-- Prove2me | Theorems.Thm_TaoBR_restr_two_mul_of_br
-- name    : TaoBR.restr_two_mul_of_br
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:06:12.29872+00:00
-- url     : https://prove2.me/theorems/eb85a3bd-32e2-48ea-bf8e-cfa90bf8ecdf
-- title:
--   Theorem 1.1 — BR(p, α) implies R(p, 2α) for p ≤ 2n/(n+1)
-- statement:
--   For $n \ge 2$, $1 \le p \le 2n/(n+1)$ and $\alpha \ge 0$: if $BR(p, \alpha)$ holds (`BR n p α`), then the localized restriction estimate $R(p, 2\alpha)$ holds (`Restr n p (2 * α)`).
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_TaoBR

open scoped ENNReal

namespace TaoBR

theorem restr_two_mul_of_br (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (α : ℝ) (hα : 0 ≤ α) :
    BR n p α → Restr n p (2 * α) := by
  sorry

end TaoBR
