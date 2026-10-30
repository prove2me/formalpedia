-- Prove2me | Theorems.Thm_TaoBR_kakeyaSetConjecture
-- name    : TaoBR.kakeyaSetConjecture
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:13:09.72781+00:00
-- url     : https://prove2.me/theorems/48e9d321-8c96-4a69-bf38-9cc6c161c747
-- title:
--   Conjecture 4.6 — every bounded Kakeya set in ℝⁿ has Minkowski dimension n
-- statement:
--   For $n \ge 2$: every bounded subset of $\mathbf R^n$ that contains a unit line segment in each direction has lower and upper Minkowski dimension $n$.
--
--   This is open for $n \ge 4$. The case $n = 2$ is Davies's theorem ([Some remarks on the Kakeya problem, Math. Proc. Cambridge Philos. Soc. 69 (1971) 417–421](https://doi.org/10.1017/S0305004100046867)), and the case $n = 3$ is the theorem of Wang and Zahl ([arXiv:2502.17655](https://arxiv.org/abs/2502.17655), 2025).
--
--   *Formalization note.* The paper's Kakeya set is "any subset $E$ of $\mathbf R^n$ which contains a unit line segment in each direction", which is `FCP.Kakeya.IsKakeya`. Minkowski dimension is defined through finite covers by small balls, which an unbounded set does not have, so the conjecture is stated for bounded sets. "Minkowski dimension $n$" is stated as: the lower and the upper Minkowski dimension both equal $n$. Compare [`FCP.Kakeya.kakeya_set_conjecture`](https://prove2.me/theorems/0b3c5537-92cc-4fab-bd57-c93d60530c59), the form with Hausdorff dimension and no boundedness assumption.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 9, Conjecture 4.6 (open)

import Mathlib
import Definitions.Def_TaoBR

namespace TaoBR

theorem kakeyaSetConjecture (n : ℕ) (hn : 2 ≤ n) : KakeyaSetConjecture n := by
  sorry

end TaoBR
