-- Prove2me | Theorems.Thm_TaoBR_br_two_zero_and_not_br_zero_of_ne_two
-- name    : TaoBR.br_two_zero_and_not_br_zero_of_ne_two
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:04:36.045927+00:00
-- url     : https://prove2.me/theorems/9f202a77-18c6-4c51-9dca-4d86ac67de61
-- title:
--   p. 1 — BR(2, 0) holds, and the Bochner–Riesz conjecture is optimal: BR(p, 0) fails for every p ≠ 2
-- statement:
--   For $n \ge 2$:
--   - $BR(2, 0)$ holds. Since $\delta(2) = 0$, this says that $S^0$, the Fourier multiplier with symbol the indicator of the open unit ball, satisfies $\|S^0 f\|_2 \le C\|f\|_2$ for all Schwartz $f$.
--   - For every $p \in [1, \infty]$ with $p \ne 2$, $BR(p, 0)$ fails: $S^{\delta(p)}$ is not bounded on $L^p$ (on Schwartz functions).
--
--   *Formalization note.* The paper says the conjecture "is optimal" apart from $BR(2, 0)$; the statement takes this to mean that the loss $\varepsilon > 0$ cannot be removed at any $p \ne 2$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 1, the trivial estimate BR(2, 0) and the optimality of the Bochner–Riesz conjecture, which cites Fefferman, The multiplier problem for the ball, Ann. of Math. 94 (1971) 330–336, https://doi.org/10.2307/1970864

import Mathlib
import Definitions.Def_TaoBR

open scoped ENNReal

namespace TaoBR

theorem br_two_zero_and_not_br_zero_of_ne_two (n : ℕ) (hn : 2 ≤ n) :
    BR n 2 0 ∧ ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ 2 → ¬ BR n p 0 := by
  sorry

end TaoBR
