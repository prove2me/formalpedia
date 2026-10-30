-- Prove2me | Theorems.Thm_TaoBR_restr_zero_of_restr
-- name    : TaoBR.restr_zero_of_restr
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:07:58.94809+00:00
-- url     : https://prove2.me/theorems/a5f1f621-d29b-4696-85fe-9666b5c88461
-- title:
--   Theorem 1.2 — R(p, α) with α ≪ 1 implies R(q, 0) for 1/q > 1/p + C/log(1/α)
-- statement:
--   For $n \ge 2$ and $1 < p < 2$ there are constants $C$ and $\alpha_0 > 0$ such that, for every $0 < \alpha < \alpha_0$: if $R(p, \alpha)$ holds, then $R(q, 0)$ holds for every $q \ge 1$ with $1/q > 1/p + C/\log(1/\alpha)$.
--
--   *Formalization note.* The constants $C$ and $\alpha_0$ (the paper's "$0 < \alpha \ll 1$") may depend on $n$ and $p$; the sentence does not say. The restriction $q \ge 1$ is the range on which $R(q, 0)$ is defined.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 2, Theorem 1.2

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem restr_zero_of_restr (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ C α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ → Restr n (ENNReal.ofReal p) α →
      ∀ q : ℝ, 1 ≤ q → 1 / p + C / Real.log (1 / α) < 1 / q → Restr n (ENNReal.ofReal q) 0 := by
  sorry

end TaoBR
