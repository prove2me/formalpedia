-- Prove2me | Theorems.Thm_TaoBR_maximalBochnerRieszConjecture_of_localSmoothingConjecture_and_bochnerRieszConjecture_of_maximalBochnerRieszConjecture
-- name    : TaoBR.maximalBochnerRieszConjecture_of_localSmoothingConjecture_and_bochnerRieszConjecture_of_maximalBochnerRieszConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:14:29.897523+00:00
-- url     : https://prove2.me/theorems/82d80b0d-031f-46f6-bd91-e89536de95d2
-- title:
--   p. 9 — local smoothing implies maximal Bochner–Riesz, and hence Bochner–Riesz
-- statement:
--   For $n \ge 2$:
--   - the local smoothing conjecture (Conjecture 4.1) implies the maximal Bochner–Riesz conjecture for $p \ge 2$ (Conjecture 4.2);
--   - the maximal Bochner–Riesz conjecture implies the Bochner–Riesz conjecture: $BR(p, \varepsilon)$ for all $1 \le p \le \infty$ and $\varepsilon > 0$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, local smoothing ⟹ maximal Bochner–Riesz, and hence Bochner–Riesz, which cites Sogge, Propagation of singularities and maximal functions in the plane, Invent. Math. 104 (1991) 349–376, https://doi.org/10.1007/BF01245080

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem maximalBochnerRieszConjecture_of_localSmoothingConjecture_and_bochnerRieszConjecture_of_maximalBochnerRieszConjecture (n : ℕ) (hn : 2 ≤ n) :
    (LocalSmoothingConjecture n → MaximalBochnerRieszConjecture n) ∧
    (MaximalBochnerRieszConjecture n → BochnerRieszConjecture n) := by
  sorry

end TaoBR
