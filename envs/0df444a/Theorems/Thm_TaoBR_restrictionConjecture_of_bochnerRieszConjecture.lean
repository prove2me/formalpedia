-- Prove2me | Theorems.Thm_TaoBR_restrictionConjecture_of_bochnerRieszConjecture
-- name    : TaoBR.restrictionConjecture_of_bochnerRieszConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:18:17.093983+00:00
-- url     : https://prove2.me/theorems/15b081cc-4b63-4f97-a828-3f3efec1a99f
-- title:
--   The Bochner–Riesz conjecture implies the restriction conjecture
-- statement:
--   For every dimension $n \ge 2$: if the Bochner–Riesz conjecture holds in $\mathbf R^n$ (`BochnerRieszConjecture n`: $BR(p, \varepsilon)$ for all $1 \le p \le \infty$ and $\varepsilon > 0$), then the restriction conjecture holds in $\mathbf R^n$ (`RestrictionConjecture n`: $R(p, 0)$ for all $1 \le p < 2n/(n+1)$).
--
--   Tao, p. 2: “In this note we present a formal proof of the implication in the reverse direction, that the Bochner-Riesz conjecture implies the restriction conjecture, as an immediate consequence of the following two results.” The title of the paper states the same implication.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 2, the implication Bochner–Riesz ⟹ restriction (the title)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem restrictionConjecture_of_bochnerRieszConjecture (n : ℕ) (hn : 2 ≤ n) :
    BochnerRieszConjecture n → RestrictionConjecture n := by
  sorry

end TaoBR
