-- Prove2me | Theorems.Thm_Trit_char3
-- name    : Trit.char3
-- status  : Proved
-- author  : @yan li
-- created : 2026-09-28T23:41:50.68985+00:00
-- url     : https://prove2.me/theorems/a92889dc-76af-4559-9a17-39e14a3f1e5d
-- title:
--   Characteristic 3 of GF(3): x + x + x = 0
-- statement:
--   In the field GF(3) = ZMod 3, every element has additive order dividing 3: x + x + x = 0. Agda proof of record: Sovereign.Algebra.ChainZ3toZ12.char3-triple (type-theory presentation-group base, Trit = GF(3)).
-- source:
--   https://github.com/triqchem-lab/discrete-mathematics (Sovereign.Algebra.ChainZ3toZ12.char3-triple)

import Mathlib

theorem Trit.char3 (x : ZMod 3) : x + x + x = 0 := by sorry
