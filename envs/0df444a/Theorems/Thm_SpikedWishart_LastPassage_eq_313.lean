-- Prove2me | Theorems.Thm_SpikedWishart_LastPassage_eq_313
-- name    : SpikedWishart.LastPassage.eq_313
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:38.505987+00:00
-- url     : https://prove2.me/theorems/315011a8-ef0d-4758-a68c-532c430ac8e9
-- title:
--   (313), p. 1693 — L(a, b) = max{L(a − 1, b), L(a, b − 1)} + X(a, b)
-- statement:
--   Let $X(i,j)$ be arbitrary real weights on the grid $\{1,\ldots,N\}\times\{1,\ldots,M\}$ and let $L(a,b)$ be the last passage time from $(1,1)$ to $(a,b)$, the maximum over up/right paths of the sum of the weights on the path. Then for every site with $a \ge 2$ and $b \ge 2$,
--   $$L(a,b) = \max\{L(a-1,b),\, L(a,b-1)\} + X(a,b).$$
--
--   This recurrence is what identifies the last passage time with the exit time of the tandem queue of §6, which satisfies the same recurrence (312).
--
--   **Formalization Note** The statement is deterministic and holds for every array of weights; the last passage time is defined as the maximum over paths (306), not by this recurrence. The paper writes the recurrence as $L(M,N) = \max\{L(M-1,N), L(M,N-1)\} + X(M,N)$ in the (customer, teller) orientation of its queueing paragraph; the recurrence is symmetric in the two coordinates, so it is stated here for (306)'s orientation, 0-based ($a, b \ge 1$).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1693, (313)

import Mathlib
import Definitions.Def_SpikedWishart_LastPassage_LPP

namespace SpikedWishart.LastPassage

/-- (313): the last passage time satisfies `L(a, b) = max{L(a-1, b), L(a, b-1)} + X(a, b)` at every
interior site (0-based, `a ≥ 1`, `b ≥ 1`). -/
theorem eq_313 {N M : ℕ} (X : Fin N → Fin M → ℝ) (a : Fin N) (b : Fin M)
    (ha : 0 < (a : ℕ)) (hb : 0 < (b : ℕ)) :
    lpp X a b =
      max (lpp X ⟨(a : ℕ) - 1, by omega⟩ b) (lpp X a ⟨(b : ℕ) - 1, by omega⟩) + X a b := by sorry

end SpikedWishart.LastPassage
