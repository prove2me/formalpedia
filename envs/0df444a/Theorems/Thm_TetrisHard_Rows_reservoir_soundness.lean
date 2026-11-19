-- Prove2me | Theorems.Thm_TetrisHard_Rows_reservoir_soundness
-- name    : TetrisHard.Rows.reservoir_soundness
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-18T20:08:18.258212+00:00
-- url     : https://prove2.me/theorems/4d73143d-2a17-4930-aad2-8369ffc01e14
-- title:
--   Theorem 6.5, no case — cumulative cleared rows bounded independently of $r$
-- statement:
--   Let $R$ be an admissible reasonable rotation model with staging allowance $\sigma$, let $P$ be a valid normalized 3-Partition instance which is a no-instance, and let $r\ge 0$. In the reservoir game of Figure 9(b) for $P$ (staging $\sigma$, reservoir height $r$, piece sequence: original pieces, one RG, $r(6s+6)/4$ squares), every attainable cleared-row count $v$ satisfies
--   $$v\le a(P)=2\,(h_0+2)+4\,(n_0+1),$$
--   where $h_0$ is the height of the original board $G(P)$ and $n_0$ the length of the original piece sequence.
--
--   Since the original board cannot be cleared, the second lock can never be opened and the reservoir is never entered. Rows cleared before the squares are bounded by the total area above the reservoir divided by the width, and, because the width $6s+7$ is odd, the squares can only complete rows that already had an odd number of filled cells when the squares began, so each of the at most $h_0+2$ rows above the reservoir is cleared at most once by squares.
--
--   **Formalization Note** The paper states the sharper bound 'at most $a$ rows', where $a$ is the number of rows at or above the second lock. The bound used here is a conservative polynomial cumulative bound, independent of $r$; it suffices for the theorem.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 6.2 (p. 21, no case of Theorem 6.3: odd width parity argument) and proof of Theorem 6.5 (p. 21: 'in the no case we can clear at most a rows'), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_GapReduction

namespace TetrisHard.Rows

theorem reservoir_soundness (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hno : ¬ P.HasSolution) (r : ℕ) :
    ∀ v, Attainable R (reservoirGame P (stagingAllowance R) r) v →
      v ≤ noBound P (stagingAllowance R) := by sorry

end TetrisHard.Rows
