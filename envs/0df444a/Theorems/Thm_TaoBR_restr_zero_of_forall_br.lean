-- Prove2me | Theorems.Thm_TaoBR_restr_zero_of_forall_br
-- name    : TaoBR.restr_zero_of_forall_br
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:08:22.954096+00:00
-- url     : https://prove2.me/theorems/39dfb4db-a583-4fda-bc01-2cfeaa12243d
-- title:
--   Corollary 1.3 — BR(p, ε) for all ε > 0 implies R(q, 0) for all 1 ≤ q < p
-- statement:
--   For $n \ge 2$ and $1 < p \le 2n/(n+1)$: if $BR(p, \varepsilon)$ holds for every $\varepsilon > 0$, then $R(q, 0)$ holds for every $1 \le q < p$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 2, Corollary 1.3

import Mathlib
import Definitions.Def_TaoBR

open scoped ENNReal

namespace TaoBR

theorem restr_zero_of_forall_br (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (h : ∀ ε : ℝ, 0 < ε → BR n p ε) :
    ∀ q : ℝ≥0∞, 1 ≤ q → q < p → Restr n q 0 := by
  sorry

end TaoBR
