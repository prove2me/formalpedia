-- Prove2me | Theorems.Thm_SP4RankNine_finite_graded_cancellation_rigidity
-- name    : SP4RankNine.finite_graded_cancellation_rigidity
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T02:00:45.428063+00:00
-- url     : https://prove2.me/theorems/76c75462-fbb6-494c-94f0-0bf1455308d0
-- title:
--   Finite graded cancellation: profile obstruction and adjacent-level rigidity
-- statement:
--   For complete finite graded cancellation pairings, the following two conclusions hold:
--   $$
--   \text{the four-top/four-bottom profile is impossible},
--   $$
--   $$
--   h=g-1,\qquad \{g\}\longrightarrow\{h\},
--   \qquad \{-h\}\longrightarrow\{-g\}
--   $$
--   in the five-level profile, with both displayed channels pairing all two atoms on each side.
--
--   More precisely, all parameters below are integers, with no bounds on the integer degree labels.
--
--   **Four-top/four-bottom obstruction.** Let $g>0$. Put four atoms at filtration $g$, with degrees $a,b,c,d$, and four at filtration $-g$, with the corresponding degrees lowered by $2g$. No involutive bijective pairing can have opposite source markers on partners, strictly decrease filtration from source to target, and decrease degree by exactly one.
--
--   **Five-level rigidity.** Assume
--   $$
--   0<h<g,\qquad c\bmod 2\ne d\bmod 2.
--   $$
--   Index the eight atoms in the following order:
--
--   | Indices | Filtration values | Integer degrees |
--   | --- | --- | --- |
--   | $0,1$ | $g,g$ | $a,b$ |
--   | $2,3$ | $h,h$ | $c,d$ |
--   | $4,5$ | $-h,-h$ | $c-2h,d-2h$ |
--   | $6,7$ | $-g,-g$ | $a-2g,b-2g$ |
--
--   For every complete graded cancellation pairing on this data, the intermediate level satisfies $h=g-1$, and the source indices are exactly
--   $$
--   \{0,1,4,5\}.
--   $$
--   The mate of each of $0,1$ belongs to $\{2,3\}$; the mate of each of $4,5$ belongs to $\{6,7\}$. Since the mate map is a bijection, these are complete two-atom pairings, not merely possible destinations.
--
--   This is one grouped finite graded cancellation theorem extracted from the rank-nine argument. It does not assert that an arbitrary knot supplies the pairing data, enumerate every rank-nine knot-Floer profile, establish the remaining central-rank-five case, or prove a knot/link realization or any smooth four-dimensional classification.
-- source:
--   Unpublished project note, gt_e12_rank18_cube_attack.md, corrected current copy, §2.1–2.2 (lines 155–194); SHA-256 ac06bc38602b5eb920f798ed749c06e06f56430eb0151d213ca2650834ccb883. Companion historical audit: gt_e12_rank18_cube_independent_audit.md, §3 (lines 137–181); SHA-256 921889fb6acd8297b81e8662c2210573f668c08a880cd65c4da62f0c22b5b0e8. The audit records corrections to an older memo hash; the selected finite cancellation argument is present in the corrected current source. Newly authored Lean formalization of this finite argument, checked on Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. No public manuscript URL, authorship priority, or novelty claim is asserted.

import Definitions.Def_SP4RankNine

set_option autoImplicit false

open SP4RankNine

theorem SP4RankNine.finite_graded_cancellation_rigidity :
    (∀ g a b c d : ℤ, 0 < g →
      ¬ Nonempty (CancellationPairing (fourFourLevel g) (fourFourMaslov g a b c d))) ∧
    (∀ g h a b c d : ℤ, 0 < h → h < g → c % 2 ≠ d % 2 →
      ∀ P : CancellationPairing (fiveLevel g h) (fiveMaslov g h a b c d),
        h = g - 1 ∧
          P.source = ![true, true, false, false, true, true, false, false] ∧
          (∀ i : Fin 8, i.val < 2 →
            2 ≤ (P.mate i).val ∧ (P.mate i).val < 4) ∧
          (∀ i : Fin 8, 4 ≤ i.val → i.val < 6 → 6 ≤ (P.mate i).val)) := by sorry
