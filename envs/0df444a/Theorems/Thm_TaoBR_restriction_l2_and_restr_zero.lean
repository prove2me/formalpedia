-- Prove2me | Theorems.Thm_TaoBR_restriction_l2_and_restr_zero
-- name    : TaoBR.restriction_l2_and_restr_zero
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:10:02.197765+00:00
-- url     : https://prove2.me/theorems/92de40b4-70ba-4951-9f74-ebfcada32fd3
-- title:
--   Tomas–Stein restriction theorem — f̂|_{S^{n−1}} ∈ L² for f ∈ Lᵖ, p ≤ 2(n+1)/(n+3), hence R(p, 0)
-- statement:
--   For $n \ge 2$ and $1 \le p \le 2(n+1)/(n+3)$:
--   - there is $C$ with $\|\hat f|_{S^{n-1}}\|_{L^2(S^{n-1})} \le C\|f\|_p$ for all Schwartz $f$;
--   - $R(p, 0)$ holds.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 2, Figure 1 (the Tomas–Stein restriction theorem), which cites Tomas, A restriction theorem for the Fourier transform, Bull. Amer. Math. Soc. 81 (1975) 477–478, https://doi.org/10.1090/S0002-9904-1975-13790-6

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR

theorem restriction_l2_and_restr_zero (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp1 : 1 ≤ p)
    (hp : p ≤ ENNReal.ofReal (2 * (n + 1) / (n + 3))) :
    (∃ C : ℝ≥0, ∀ f : 𝓢(E n, ℂ),
      eLpNorm (restriction f) 2 (sphereMeasure n) ≤ C * eLpNorm f p volume) ∧
    Restr n p 0 := by
  sorry

end TaoBR
