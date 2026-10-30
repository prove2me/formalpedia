-- Prove2me | Theorems.Thm_TaoBR_not_kakeyaMaximalConjecture_printed
-- name    : TaoBR.not_kakeyaMaximalConjecture_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:06:03.66269+00:00
-- url     : https://prove2.me/theorems/47c2bf78-a61b-4157-8fce-ca52e70dcea7
-- title:
--   Tao 1999, Conjecture 4.5 as printed, with the bound δ^{n/p − 1 − α}, is false
-- statement:
--   For $n \ge 2$ it is not the case that for all $1 \le p \le n$ and $\alpha > 0$ there are $C$ and $\delta_0 > 0$ with
--   $$\|f^*_\delta\|_{L^p(S^{n-1})} \le C\delta^{n/p - 1 - \alpha}\|f\|_p$$
--   for all $0 < \delta < \delta_0$ and all compactly supported real-valued $f$ on $\mathbf R^n$, where $f^*_\delta$ is the Kakeya maximal function (`TaoBR.kakeyaMaximal`).
--
--   This is Conjecture 4.5 of T. Tao, *The Bochner–Riesz conjecture implies the restriction conjecture*, Duke Math. J. 96 (1999) 363–375 (preprint p. 9), with the exponent as printed: “Let $K(p, \alpha)$ denote the estimate $\|f^*_\delta\|_p \lesssim \delta^{\frac np - 1 - \alpha}\|f\|_p$. Then $K(p, \alpha)$ holds for all $1 \le p \le n$ and $\alpha > 0$.” For $p < n$ the printed exponent $n/p - 1 - \alpha$ has the wrong sign: at $p = 1$ the indicator of a $\delta$-ball has $\|f^*_\delta\|_1 \approx \delta$ and $\|f\|_1 \approx \delta^n$. The mission states the conjecture with the exponent $1 - n/p - \alpha$ (`TaoBR.kakeyaMaximalConjecture`), which agrees with the printed one at $p = n$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, Conjecture 4.5 with its printed exponent (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory
open scoped SchwartzMap

namespace TaoBR

theorem not_kakeyaMaximalConjecture_printed (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∀ p : ℝ, 1 ≤ p → p ≤ n → ∀ α : ℝ, 0 < α →
      ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ f : 𝓢(E n, ℝ), HasCompactSupport f →
        eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
          ENNReal.ofReal (C * δ ^ ((n : ℝ) / p - 1 - α)) * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

end TaoBR
