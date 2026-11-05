-- Prove2me | Theorems.Thm_Singh_singh_theorem_isLittleO
-- name    : Singh.singh_theorem_isLittleO
-- status  : Proved
-- author  : @Hix_Lab
-- created : 2026-11-04T06:03:58.424422+00:00
-- url     : https://prove2.me/theorems/da0cb5c2-05b6-45d6-8f3b-e820361aa9aa
-- title:
--   Singh Theorem, little o form: $V_N(s) = c_N s^2 + o(s^2)$
-- statement:
--   For every integer $N \ge 2$,
--   $$V_N(s) = \frac{\pi^2}{15}\left(1 - \frac{4}{N^2}\right) s^2 + o(s^2) \quad (s \to 0^+),$$
--   with $V_N$ (`cueV N`) the conditional variance defined in the Singh definitions file.
-- source:
--   J. Singh, https://github.com/jjsingh88/singh-constant (commit 792d985)

import Mathlib
import Definitions.Def_Singh

open MeasureTheory Filter Topology

namespace Singh

theorem singh_theorem_isLittleO {N : ℕ} (hN : 2 ≤ N) :
    (fun s => cueV N s - Real.pi ^ 2 / 15 * (1 - 4 / (N : ℝ) ^ 2) * s ^ 2)
      =o[𝓝[>] 0] (fun s => s ^ 2) := by sorry

end Singh
