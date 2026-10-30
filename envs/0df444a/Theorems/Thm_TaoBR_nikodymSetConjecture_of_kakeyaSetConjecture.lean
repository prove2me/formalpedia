-- Prove2me | Theorems.Thm_TaoBR_nikodymSetConjecture_of_kakeyaSetConjecture
-- name    : TaoBR.nikodymSetConjecture_of_kakeyaSetConjecture
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:17:52.500998+00:00
-- url     : https://prove2.me/theorems/5d5272ee-a97d-4e84-9781-d03a3debfb4e
-- title:
--   Figure 2 — the Kakeya set conjecture implies the Nikodym set conjecture
-- statement:
--   For $n \ge 2$: if every bounded Kakeya set in $\mathbf R^n$ has lower and upper Minkowski dimension $n$ (Conjecture 4.6), then every bounded Nikodym set in $\mathbf R^n$ has lower and upper Minkowski dimension $n$ (Conjecture 4.8).
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 10, Figure 2 (Kakeya set ⟹ Nikodym set)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem nikodymSetConjecture_of_kakeyaSetConjecture (n : ℕ) (hn : 2 ≤ n) :
    KakeyaSetConjecture n → NikodymSetConjecture n := by
  sorry

end TaoBR
