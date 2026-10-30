-- Prove2me | Theorems.Thm_TaoBR_restr_sparse_of_restr
-- name    : TaoBR.restr_sparse_of_restr
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:06:40.500983+00:00
-- url     : https://prove2.me/theorems/bf049406-71f0-49eb-b4fe-15137d633ca6
-- title:
--   Lemma 3.2 — R(p, α) extends to functions supported on a sparse union of R-balls
-- statement:
--   For $n \ge 2$, $1 < p < 2$ and $\alpha > 0$: if $R(p, \alpha)$ holds, then there are constants $C_0$ and $C$ such that for every $R \ge 1$, every $N$, and every family of centres $x_1, \dots, x_N$ forming a sparse collection with constant $C_0$ (distinct centres at distance at least $R^{C_0}N^{C_0}$), every Schwartz $f$ supported in $\bigcup_i \overline B(x_i, R)$ satisfies
--   $$\|\Re f\|_{L^p(S^{n-1})} \le C R^\alpha\|f\|_p.$$
--
--   *Formalization note.* Definition 3.1's constant ("$C$ denotes a constant that will change from line to line") is the sparseness constant $C_0$; the lemma provides some $C_0$ for which the bound holds. Lemma 3.3 produces sparse collections for every prescribed constant, so the two fit together.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 5, Lemma 3.2

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR

theorem restr_sparse_of_restr (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p) (hp2 : p < 2)
    (α : ℝ) (hα : 0 < α) (h : Restr n p α) :
    ∃ C₀ : ℝ, ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse C₀ R x →
      ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
        eLpNorm (restriction f) p (sphereMeasure n) ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f p volume := by
  sorry

end TaoBR
