-- Prove2me | Theorems.Thm_TaoBR_restr_sparse_of_restr_uniform
-- name    : TaoBR.restr_sparse_of_restr_uniform
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T22:55:21.758703+00:00
-- url     : https://prove2.me/theorems/e6bd5d56-5030-4eda-a3d5-31e2e544726d
-- title:
--   Tao 1999, Lemma 3.2 with the sparseness exponent uniform in α
-- statement:
--   For $n \ge 2$ and $1 < p < 2$ there is a sparseness exponent $C_0$ such that, for every $\alpha > 0$ for which $R(p, \alpha)$ holds, there is a constant $C$ with the following property. For every $R \ge 1$, every $N$, and every family of centres $x_1, \dots, x_N$ at mutual distances at least $R^{C_0}N^{C_0}$, every Schwartz $f$ supported in $\bigcup_i \overline B(x_i, R)$ satisfies
--   $$\|\Re f\|_{L^p(S^{n-1})} \le C R^\alpha\|f\|_p.$$
--
--   This is Lemma 3.2 of T. Tao, *The Bochner–Riesz conjecture implies the restriction conjecture*, Duke Math. J. 96 (1999) 363–375 (preprint p. 5), with the order of the constants made explicit: $C_0$ is chosen before $\alpha$. The paper's proof gives this order. Its sparseness constant comes from the decay of $\widehat{d\sigma}$ and depends only on the dimension. The order matters for Theorem 1.2: there the radii of the sparse collections from Lemma 3.3 grow like $|E|^{C^N}$, with $C$ depending on the sparseness exponent, and $N$ is taken comparable to $\log(1/\alpha)$. So Theorem 1.2 needs a sparseness exponent that does not grow as $\alpha \to 0$. The mission's Lemma 3.2 (`TaoBR.restr_sparse_of_restr`) chooses its $C_0$ after $\alpha$, and follows from this statement.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 5, Lemma 3.2 with the sparseness exponent chosen before alpha (the order its proof gives and Theorem 1.2 uses)

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR

theorem restr_sparse_of_restr_uniform (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p)
    (hp2 : p < 2) :
    ∃ C₀ : ℝ, ∀ α : ℝ, 0 < α → Restr n p α →
      ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse C₀ R x →
        ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
          eLpNorm (restriction f) p (sphereMeasure n) ≤
            C * ENNReal.ofReal (R ^ α) * eLpNorm f p volume := by
  sorry

end TaoBR
