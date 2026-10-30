-- Prove2me | Theorems.Thm_TaoBR_restrictionConjectures_imply_kakeyaMaximal_and_maximalConjectures_imply_setConjectures
-- name    : TaoBR.restrictionConjectures_imply_kakeyaMaximal_and_maximalConjectures_imply_setConjectures
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:14:51.924043+00:00
-- url     : https://prove2.me/theorems/fa7ecdcb-bb3c-4dba-aa39-aa1f1b79afb8
-- title:
--   p. 9 — spherical and parabolic restriction each imply Kakeya maximal; Kakeya (Nikodym) maximal implies the Kakeya (Nikodym) set conjecture
-- statement:
--   For $n = m + 1$ with $m \ge 1$ (so $n \ge 2$), all in $\mathbf R^n$:
--   - the restriction conjecture (`RestrictionConjecture n`) implies the Kakeya maximal conjecture (Conjecture 4.5);
--   - the parabolic restriction conjecture (Conjecture 4.4, with the critical exponent $2n/(n+1)$) implies the Kakeya maximal conjecture;
--   - the Kakeya maximal conjecture implies that every bounded Kakeya set has lower and upper Minkowski dimension $n$ (Conjecture 4.6);
--   - the Nikodym maximal conjecture (Conjecture 4.7) implies that every bounded Nikodym set has lower and upper Minkowski dimension $n$ (Conjecture 4.8).
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, restriction ⟹ Kakeya maximal ⟹ Kakeya set, Nikodym maximal ⟹ Nikodym set, which cites Fefferman, A note on spherical summation multipliers, Israel J. Math. 15 (1973) 44–52, https://doi.org/10.1007/BF02771772, Córdoba, The Kakeya maximal function and spherical summation multipliers, Amer. J. Math. 99 (1977) 1–22, https://doi.org/10.2307/2374006, and Bourgain, Besicovitch type maximal operators and applications to Fourier analysis, Geom. Funct. Anal. 1 (1991) 147–187, https://doi.org/10.1007/BF01896376

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem restrictionConjectures_imply_kakeyaMaximal_and_maximalConjectures_imply_setConjectures (m : ℕ) (hm : 1 ≤ m) :
    (RestrictionConjecture (m + 1) → KakeyaMaximalConjecture (m + 1)) ∧
    (ParabolicRestrictionConjecture m → KakeyaMaximalConjecture (m + 1)) ∧
    (KakeyaMaximalConjecture (m + 1) → KakeyaSetConjecture (m + 1)) ∧
    (NikodymMaximalConjecture (m + 1) → NikodymSetConjecture (m + 1)) := by
  sorry

end TaoBR
