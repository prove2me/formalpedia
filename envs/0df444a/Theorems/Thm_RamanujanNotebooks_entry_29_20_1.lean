-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_29_20_1
-- name    : RamanujanNotebooks.entry_29_20_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T22:34:18.40443+00:00
-- url     : https://prove2.me/theorems/48e9e89b-8907-4dda-8ed1-30aec7cc26ef
-- title:
--   Ramanujan series for 1/π (20.1)
-- statement:
--   With absolute convergence, 4/π = ∑_{n≥0} (6n+1) (½)_n³ / (4^n (n!)³) (formula written in plain notation; $(a)_n$ is the rising factorial).
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 29, Entry 20 (20.1), p. 352, eq. (20.1).

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorialR

namespace RamanujanNotebooks
theorem entry_29_20_1 :
    HasSum
      (fun n : ℕ =>
        (6 * (n : ℝ) + 1) * shiftedFactorialR (1 / 2) n ^ 3
          / (4 ^ n * (n.factorial : ℝ) ^ 3))
      (4 / Real.pi) := by sorry
end RamanujanNotebooks
