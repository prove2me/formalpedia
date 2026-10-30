-- Prove2me | Theorems.Thm_TaoBR_nikodymSetConjecture
-- name    : TaoBR.nikodymSetConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:14:06.179278+00:00
-- url     : https://prove2.me/theorems/a00a89a3-771a-43ab-99fb-56467efa2d3d
-- title:
--   Conjecture 4.8 — every bounded Nikodym set in ℝⁿ has Minkowski dimension n
-- statement:
--   For $n \ge 2$: let $E \subseteq \mathbf R^n$ be bounded and such that every $x \in \mathbf R^n$ lies on a line $l$ for which $E \cap l$ contains a unit line segment. Then $E$ has lower and upper Minkowski dimension $n$.
--
--   This is open for $n \ge 3$; the case $n = 2$ is classical.
--
--   *Formalization note.* As for Conjecture 4.6, Minkowski dimension is defined for bounded sets, and "Minkowski dimension $n$" is stated as: the lower and the upper Minkowski dimension both equal $n$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, Conjecture 4.8 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem nikodymSetConjecture (n : ℕ) (hn : 2 ≤ n) : NikodymSetConjecture n := by
  sorry

end TaoBR
