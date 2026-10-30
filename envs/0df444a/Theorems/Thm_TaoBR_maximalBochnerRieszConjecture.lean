-- Prove2me | Theorems.Thm_TaoBR_maximalBochnerRieszConjecture
-- name    : TaoBR.maximalBochnerRieszConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:11:09.988017+00:00
-- url     : https://prove2.me/theorems/4dd7f2a6-80a5-4d03-99a4-c7fd221ea4d2
-- title:
--   Conjecture 4.2 — maximal spherical Bochner–Riesz for p ≥ 2
-- statement:
--   For $n \ge 2$, every $2 \le p \le \infty$ and every $\delta > \delta(p)$, there is $C$ such that every Schwartz $f$ satisfies
--   $$\Big\|\sup_{R > 0}|S^\delta_R f|\Big\|_p \le C\|f\|_p,$$
--   where $S^\delta_R$ is the multiplier with symbol $(1 - |\xi/R|^2)_+^\delta$.
--
--   This is open for $n \ge 3$. For $n = 2$ it follows from Carbery's $L^4$ theorem ([The boundedness of the maximal Bochner–Riesz operator on $L^4(\mathbf R^2)$, Duke Math. J. 50 (1983) 409–416](https://doi.org/10.1215/S0012-7094-83-05018-4), the paper's [3]).
--
--   *Formalization note.* The paper writes $\sup_{R>0} S^\delta_R f$; since $S^\delta_R f$ is complex-valued, the supremum is taken of absolute values.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 8, Conjecture 4.2 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem maximalBochnerRieszConjecture (n : ℕ) (hn : 2 ≤ n) :
    MaximalBochnerRieszConjecture n := by
  sorry

end TaoBR
