-- Prove2me | Theorems.Thm_TaoBR_not_parabolicRestriction_printed
-- name    : TaoBR.not_parabolicRestriction_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:05:56.661736+00:00
-- url     : https://prove2.me/theorems/517d7ce2-e6a8-4a1a-83a7-c900c57c57bb
-- title:
--   Tao 1999, Conjecture 4.4 as printed, with the range 1 ≤ p < 2n/(n−1), is false
-- statement:
--   Write $\mathbf R^n = \mathbf R^m \times \mathbf R$ with $n = m + 1$ and $m \ge 1$. It is not the case that for every $1 \le p < 2n/(n-1)$ there is $C$ such that every Schwartz $f$ on $\mathbf R^n$ satisfies
--   $$\Big(\int_{|\underline\xi| \le 1}\big|\hat f(\underline\xi, \tfrac12|\underline\xi|^2)\big|^p\,d\underline\xi\Big)^{1/p} \le C\|f\|_p.$$
--
--   This is Conjecture 4.4 of T. Tao, *The Bochner–Riesz conjecture implies the restriction conjecture*, Duke Math. J. 96 (1999) 363–375 (preprint p. 8), with the range of $p$ as printed: “Then for all $1 \le p < 2n/(n-1)$ we have $\|\hat f|_S\|_{L^p(S)} \lesssim \|f\|_p$.” The printed range contains $p = 2n/(n+1)$, where the estimate fails. The paper's mission states the conjecture with the critical exponent $2n/(n+1)$ (`TaoBR.parabolicRestrictionConjecture`).
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 8, Conjecture 4.4 with its printed range (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR

theorem not_parabolicRestriction_printed (m : ℕ) (hm : 1 ≤ m) :
    ¬ ∀ p : ℝ≥0∞, 1 ≤ p → p < ENNReal.ofReal (2 * (m + 1) / m) → ∃ C : ℝ≥0,
      ∀ f : 𝓢(E (m + 1), ℂ),
        eLpNorm (paraboloidRestriction f) p (volume.restrict (closedBall (0 : E m) 1)) ≤
          C * eLpNorm f p volume := by
  sorry

end TaoBR
