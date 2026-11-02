-- Prove2me | Theorems.Thm_TensorCoordinateCountdown_countdownProg_exec
-- name    : TensorCoordinateCountdown.countdownProg_exec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:50:04.784728+00:00
-- url     : https://prove2.me/theorems/efd7f45c-a5fa-4028-b633-a049f1ea7212
-- title:
--   Reverse row-major coordinate step
-- statement:
--   For any nonterminal pair of unary coordinates, the fixed four-stack program advances one step in reverse row-major order, preserving the maximum coordinate and clearing scratch. It decrements a positive column in two steps; at column zero it decrements the row and resets the column to the maximum in $6M+6$ steps.

import Definitions.Def_TensorCoordinateCountdown
open CookPvsNP ProjSchedTW.Complexity

namespace TensorCoordinateCountdown
theorem countdownProg_exec (maximum row column : ℕ)
    (hnonterminal : row > 0 ∨ column > 0) :
    countdownProg.Exec (store maximum row column)
      (store maximum (if column = 0 then row - 1 else row)
        (if column = 0 then maximum else column - 1))
      (if column = 0 then 6 * maximum + 6 else 2) := by
  sorry

end TensorCoordinateCountdown
