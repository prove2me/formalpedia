-- Prove2me | Theorems.Thm_TaoBR_not_restr_zero_of_le
-- name    : TaoBR.not_restr_zero_of_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:08:57.100108+00:00
-- url     : https://prove2.me/theorems/cfa0daf8-ba08-4074-a8c8-e2d14e0362cc
-- title:
--   p. 2 — R(p, 0) is false for every p ≥ 2n/(n+1)
-- statement:
--   For $n \ge 2$ and every $p \ge 2n/(n+1)$ (including $p = \infty$), the restriction estimate $R(p, 0)$ fails.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 2, optimality of the exponent

import Mathlib
import Definitions.Def_TaoBR

open scoped ENNReal

namespace TaoBR

theorem not_restr_zero_of_le (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal (2 * n / (n + 1)) ≤ p) : ¬ Restr n p 0 := by
  sorry

end TaoBR
