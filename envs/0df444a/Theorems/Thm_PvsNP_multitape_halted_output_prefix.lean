-- Prove2me | Theorems.Thm_PvsNP_multitape_halted_output_prefix
-- name    : PvsNP.multitape_halted_output_prefix
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T10:06:49.294197+00:00
-- url     : https://prove2.me/theorems/9bd631f5-0218-46c4-a665-a6ffe5cdf2bf
-- title:
--   A halted multitape simulation determines every output prefix
-- statement:
--   Suppose a deterministic multitape simulation halts with output list $y$ by some time $t$. At every observation time $s$, its output list is a prefix of $y$. If it has already halted by time $s$, its entire simulator result at $s$ is the same halted result with output $y$. Observation times on either side of $t$ are allowed.
-- source:
--   Consequence of the append-only output and absorbing halt semantics of `step`, `stepOut`, and `simulate` in the Prove2Me multitape universal simulator, https://prove2.me/api/v1/definitions/0f28a4fa-b44a-4f88-8354-43271be0fd47.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib
open Turing.MultiTapeTM.Universal

theorem PvsNP.multitape_halted_output_prefix (d : Desc) (x output : List ℕ) {t : ℕ}
    (finished : simulate d x t = (output,true)) :
    ∀ s, ((simulate d x s).1 <+: output) ∧
      ((simulate d x s).2 = true → simulate d x s = (output,true)) := by sorry
