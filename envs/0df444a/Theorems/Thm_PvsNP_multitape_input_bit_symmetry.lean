-- Prove2me | Theorems.Thm_PvsNP_multitape_input_bit_symmetry
-- name    : PvsNP.multitape_input_bit_symmetry
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T10:27:29.403913+00:00
-- url     : https://prove2.me/theorems/ae33125f-5651-5bcf-ac81-6379583574be
-- title:
--   Input-bit symmetry makes multitape runs equal on equal-length words
-- statement:
--   Consider the deterministic multitape simulator with binary input. Assume that for every control state and every vector of work-tape reads, the first matching table actions for reading $0$ and $1$ are equal, with a missing entry considered as no action. Then the simulator gives the same output and halt flag after any fixed number of steps on any two binary words of equal length.
-- source:
--   Derived from `inputSymbol`, `moveInput`, `stepWith`, and `simulate` in the Prove2Me universal multitape semantics, https://prove2.me/api/v1/definitions/0f28a4fa-b44a-4f88-8354-43271be0fd47.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib
open Turing.MultiTapeTM.Universal

theorem PvsNP.multitape_input_bit_symmetry (d : Desc)
    (symmetric : ∀ (q : ℕ) (reads : List (Option ℕ)),
      (d.table.find? (fun row => decide (row.1 = ⟨q,some 0,reads⟩))).map Prod.snd =
      (d.table.find? (fun row => decide (row.1 = ⟨q,some 1,reads⟩))).map Prod.snd)
    (w v : List Bool) (len : w.length = v.length) (t : ℕ) :
    simulate d (w.map Bool.toNat) t = simulate d (v.map Bool.toNat) t := by sorry
