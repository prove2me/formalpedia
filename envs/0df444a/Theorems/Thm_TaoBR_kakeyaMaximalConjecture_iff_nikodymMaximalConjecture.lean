-- Prove2me | Theorems.Thm_TaoBR_kakeyaMaximalConjecture_iff_nikodymMaximalConjecture
-- name    : TaoBR.kakeyaMaximalConjecture_iff_nikodymMaximalConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:17:27.985139+00:00
-- url     : https://prove2.me/theorems/1046ca61-753c-400b-ac29-237eedc28465
-- title:
--   p. 11 — the Kakeya and Nikodym maximal function conjectures are equivalent
-- statement:
--   For $n \ge 2$: the Kakeya maximal conjecture (Conjecture 4.5) holds in $\mathbf R^n$ if and only if the Nikodym maximal conjecture (Conjecture 4.7) holds in $\mathbf R^n$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 11, the equivalence of the Kakeya and Nikodym maximal conjectures

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem kakeyaMaximalConjecture_iff_nikodymMaximalConjecture (n : ℕ) (hn : 2 ≤ n) :
    KakeyaMaximalConjecture n ↔ NikodymMaximalConjecture n := by
  sorry

end TaoBR
