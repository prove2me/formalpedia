-- Prove2me | Theorems.Thm_TaoBR_parabolicRestrictionConjecture_iff_parabolicBochnerRieszConjecture
-- name    : TaoBR.parabolicRestrictionConjecture_iff_parabolicBochnerRieszConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:15:41.795358+00:00
-- url     : https://prove2.me/theorems/aa99aa7c-85f5-4175-8b41-dad69ed1d880
-- title:
--   p. 10 — for paraboloids, the Bochner–Riesz and restriction conjectures are equivalent
-- statement:
--   For $n = m + 1$ with $m \ge 1$: the parabolic restriction conjecture (Conjecture 4.4, with the critical exponent $2n/(n+1)$) holds if and only if the parabolic Bochner–Riesz conjecture (Conjecture 4.3) holds.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 10, the equivalence of the Bochner–Riesz and restriction conjectures for paraboloids

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem parabolicRestrictionConjecture_iff_parabolicBochnerRieszConjecture (m : ℕ) (hm : 1 ≤ m) :
    ParabolicRestrictionConjecture m ↔ ParabolicBochnerRieszConjecture m := by
  sorry

end TaoBR
