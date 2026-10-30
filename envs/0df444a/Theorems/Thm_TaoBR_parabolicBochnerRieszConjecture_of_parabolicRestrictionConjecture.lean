-- Prove2me | Theorems.Thm_TaoBR_parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture
-- name    : TaoBR.parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:15:15.43525+00:00
-- url     : https://prove2.me/theorems/9acdf5b6-5b27-48e5-8ab5-4e65866360aa
-- title:
--   p. 9 — the parabolic restriction conjecture implies the parabolic Bochner–Riesz conjecture (Carbery)
-- statement:
--   For $n = m + 1$ with $m \ge 1$: if the parabolic restriction conjecture (Conjecture 4.4, with the critical exponent $2n/(n+1)$) holds, then the parabolic Bochner–Riesz conjecture (Conjecture 4.3) holds.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, parabolic restriction ⟹ parabolic Bochner–Riesz, which cites Carbery, Restriction implies Bochner–Riesz for paraboloids, Math. Proc. Cambridge Philos. Soc. 111 (1992) 525–529, https://doi.org/10.1017/S0305004100075599

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture (m : ℕ) (hm : 1 ≤ m) :
    ParabolicRestrictionConjecture m → ParabolicBochnerRieszConjecture m := by
  sorry

end TaoBR
