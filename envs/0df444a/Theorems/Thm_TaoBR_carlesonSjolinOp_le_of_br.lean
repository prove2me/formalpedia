-- Prove2me | Theorems.Thm_TaoBR_carlesonSjolinOp_le_of_br
-- name    : TaoBR.carlesonSjolinOp_le_of_br
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:05:14.794158+00:00
-- url     : https://prove2.me/theorems/d4796663-8e19-4c36-a959-f6a9342637c4
-- title:
--   p. 3 — the Carleson–Sjölin reduction: BR(p, α) bounds the oscillatory integral G_R
-- statement:
--   Let $n \ge 2$, $1 \le p \le 2n/(n+1)$, $\alpha \ge 0$, and suppose $BR(p, \alpha)$ holds. Let $\psi : \mathbf R^n \times \mathbf R^n \to \mathbf R$ be smooth and compactly supported, with $|x - y| \ge c$ on its support for some $c > 0$. Then there is $C$ such that for every $R \ge 1$ and every Schwartz $f$,
--   $$\|G_R f\|_p \le C R^{-n/p'} R^{\alpha}\|f\|_p, \qquad G_R f(x) = \int e^{2\pi i R|x-y|}\psi(x,y)f(y)\,dy.$$
--
--   *Formalization note.* The paper's "bump function supported on the set $|x|, |y| \lesssim 1$, $|x-y| \sim 1$" is read as: any smooth compactly supported real function whose support stays a positive distance from the diagonal. Compact support gives $|x|, |y|, |x - y| \lesssim 1$. The estimate is claimed for every such $\psi$, uniformly in $R \ge 1$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 3, the Carleson–Sjölin reduction, which cites Stein, Harmonic Analysis (1993), Córdoba (1977) and Carleson–Sjölin (1972)

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR

theorem carlesonSjolinOp_le_of_br (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (α : ℝ) (hα : 0 ≤ α) (hBR : BR n p α)
    (ψ : E n → E n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψd : ∃ c : ℝ, 0 < c ∧ ∀ x y, ψ x y ≠ 0 → c ≤ ‖x - y‖) :
    ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ),
      eLpNorm (carlesonSjolinOp ψ R f) p volume ≤
        C * ENNReal.ofReal (R ^ (-((n : ℝ) * (conjExp p)⁻¹.toReal))) * ENNReal.ofReal (R ^ α) *
          eLpNorm f p volume := by
  sorry

end TaoBR
