-- Prove2me | Theorems.Thm_TaoBR_parabolicRestrictionConjecture_of_restrictionConjecture
-- name    : TaoBR.parabolicRestrictionConjecture_of_restrictionConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:16:09.515191+00:00
-- url     : https://prove2.me/theorems/7db88f36-0e3d-4efb-88f4-a827daba3aed
-- title:
--   pp. 10–11 — the spherical restriction conjecture implies the parabolic restriction conjecture
-- statement:
--   For $n = m + 1$ with $m \ge 1$: if the restriction conjecture holds in $\mathbf R^n$ (`RestrictionConjecture n`), then the parabolic restriction conjecture (Conjecture 4.4, with the critical exponent $2n/(n+1)$) holds.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), pp. 10–11, spherical restriction ⟹ parabolic restriction

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem parabolicRestrictionConjecture_of_restrictionConjecture (m : ℕ) (hm : 1 ≤ m) :
    RestrictionConjecture (m + 1) → ParabolicRestrictionConjecture m := by
  sorry

end TaoBR
