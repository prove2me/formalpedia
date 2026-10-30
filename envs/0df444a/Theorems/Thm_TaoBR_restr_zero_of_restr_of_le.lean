-- Prove2me | Theorems.Thm_TaoBR_restr_zero_of_restr_of_le
-- name    : TaoBR.restr_zero_of_restr_of_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:09:26.829983+00:00
-- url     : https://prove2.me/theorems/8c9f7a1c-49ce-4855-b690-ab8ff7e538c6
-- title:
--   Theorem 1.4 (Bourgain) — R(p, α) implies R(q, 0) for q′ ≥ 2 + 1/((n+1)/(2p′) − α)
-- statement:
--   For $n \ge 2$, $1 \le p \le 2(n+1)/(n+3)$ and $0 \le \alpha \le (n+1)/(2p')$: if $R(p, \alpha)$ holds, then $R(q, 0)$ holds for every $q \ge 1$ whose conjugate exponent satisfies
--   $$q' \ge 2 + \frac{1}{\frac{n+1}{2p'} - \alpha}.$$
--   The arithmetic is in $[0, \infty]$: at $\alpha = (n+1)/(2p')$ the right side is $\infty$, and the condition holds only for $q = 1$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 3, Theorem 1.4 (Bourgain), which cites Bourgain, Some new estimates on oscillatory integrals, Essays on Fourier Analysis in Honor of Elias M. Stein (1995) 83–112

import Mathlib
import Definitions.Def_TaoBR

open scoped ENNReal

namespace TaoBR

theorem restr_zero_of_restr_of_le (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp1 : 1 ≤ p)
    (hp : p ≤ ENNReal.ofReal (2 * (n + 1) / (n + 3))) (α : ℝ) (hα : 0 ≤ α)
    (hα' : α ≤ ((n : ℝ) + 1) / 2 * (conjExp p)⁻¹.toReal) (h : Restr n p α) :
    ∀ q : ℝ≥0∞, 1 ≤ q →
      2 + (ENNReal.ofReal (((n : ℝ) + 1) / 2 * (conjExp p)⁻¹.toReal - α))⁻¹ ≤ conjExp q →
        Restr n q 0 := by
  sorry

end TaoBR
