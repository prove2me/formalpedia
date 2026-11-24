-- Prove2me | Theorems.Thm_P2M_Combinatorics_Line_exists_mono_of_ack_le__0a26130f3292
-- name    : P2M_Combinatorics_Line_exists_mono_of_ack_le__0a26130f3292
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:51:15.594484+00:00
-- url     : https://prove2.me/theorems/2926fde3-170a-4db6-b312-2cf855357429
-- title:
--   P2 M Combinatorics Line exists mono of ack le  0a26130f3292: P2 M Combinatorics Line exists mono of ack le  0a26130f3292
-- statement:
--   **Shelah's theorem.** For `k ≥ 1` letters, `r` colors and `n ≥ ack 5 (2 * k + r)`, every
--   coloring of the words of length `n` has a monochromatic combinatorial line.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/Solution.lean#L25-L28
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/Solution.lean#L25-L28

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_Ackermann
public import Definitions.Def_ShelahHalesJewett_Solution
set_option autoImplicit true
@[expose] public section
public section
open Combinatorics Combinatorics.Line

theorem P2M_Combinatorics_Line_exists_mono_of_ack_le__0a26130f3292 {k r n : ℕ} (hk : 0 < k) (hn : ack 5 (2 * k + r) ≤ n)
    (C : (Fin n → Fin k) → Fin r) : ∃ l : Line (Fin k) (Fin n), l.IsMono C := by sorry

alias «Combinatorics».«Line».«exists_mono_of_ack_le'» := P2M_Combinatorics_Line_exists_mono_of_ack_le__0a26130f3292
