-- Prove2me | Theorems.Thm_SZ_strace_emod
-- name    : SZ.strace_emod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:49:20.189661+00:00
-- url     : https://prove2.me/theorems/edfe5e52-75a5-4255-89db-ea54406ccac4
-- title:
--   SZ: strace emod
-- statement:
--   **The trace is `≡ 2` modulo `6`.**  `S_{n+2} = 2S_{n+1} + 2S_n` with `S₀ = S₁ = 2`
--   propagates `2 · 2 + 2 · 2 = 8 ≡ 2`.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L73-L77
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadThm6.lean#L73-L77

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
set_option autoImplicit false
open SZ
open Real

theorem SZ.strace_emod (n : ℕ) : rec2 2 2 2 2 n % 6 = 2 := by sorry
