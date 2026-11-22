-- Prove2me | Theorems.Thm_SZ_natCast_mem_MahlerZ
-- name    : SZ.natCast_mem_MahlerZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:41:14.483812+00:00
-- url     : https://prove2.me/theorems/43461d3c-2c02-449d-8aaf-7c11d1e5d18d
-- title:
--   SZ: nat Cast mem Mahler Z
-- statement:
--   Every integer `g ≥ 2` lies in `𝒵`: take `ξ = 2`, so that `⌊2 gⁿ⌋ = 2 gⁿ`
--   ([Dub06EO] p. 331).
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L106-L110
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean#L106-L110

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Defs
set_option autoImplicit false
open SZ
open Int

theorem SZ.natCast_mem_MahlerZ {g : ℕ} (hg : 2 ≤ g) : (g : ℝ) ∈ MahlerZ := by sorry
