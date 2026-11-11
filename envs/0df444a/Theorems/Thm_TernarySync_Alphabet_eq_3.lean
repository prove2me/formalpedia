-- Prove2me | Theorems.Thm_TernarySync_Alphabet_eq_3
-- name    : TernarySync.Alphabet.eq_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:51:55.428705+00:00
-- url     : https://prove2.me/theorems/48008b79-82df-48df-9a62-ef8e6a194616
-- title:
--   Eq. (3) — $\mathrm{ED}(x,y) = |x| + |y| - 2\,\mathrm{LCS}(x,y)$
-- statement:
--   For finite words $x$ and $y$ over any alphabet, the insertion–deletion distance $\mathrm{ED}(x,y)$ (the least number of single-symbol insertions and deletions turning $x$ into $y$) and the longest common subsequence length $\mathrm{LCS}(x,y)$ satisfy
--
--   $$\mathrm{ED}(x,y) = |x| + |y| - 2\,\mathrm{LCS}(x,y).$$
--
--   This standard identity (§2.1, Equation (3)) converts the paper's LCS bounds into edit-distance bounds: for adjacent intervals of equal length $\ell$, $\mathrm{LCS} \le (1-\eta)\ell$ is the same as $\mathrm{ED} \ge 2\eta\ell$.
--
--   **Formalization Note.** The identity is stated in $\mathbb{Z}$, so the subtraction is not truncated.
--
--   Differences from the source:
--   - encoding: an identity of natural numbers with a subtraction → the same identity with both sides cast to ℤ; reason: avoids truncated natural subtraction; the right side is nonnegative anyway, so the identity is the same
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 13 (PDF 14), §2.1, Eq. (3)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_EditDistance

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Equation (3) (§2.1, p. 13): for all finite words `x`, `y` over any alphabet,
`ED(x, y) = |x| + |y| − 2 LCS(x, y)`, where `ED` is the insertion–deletion distance. -/
theorem eq_3 {α : Type*} (x y : List α) :
    (ed x y : ℤ) = (x.length : ℤ) + (y.length : ℤ) - 2 * (lcs x y : ℤ) := by sorry

end TernarySync.Alphabet
