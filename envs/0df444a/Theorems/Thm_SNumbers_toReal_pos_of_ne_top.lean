-- Prove2me | Theorems.Thm_SNumbers_toReal_pos_of_ne_top
-- name    : SNumbers.toReal_pos_of_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:06:03.843254+00:00
-- url     : https://prove2.me/theorems/fc497a43-e314-4f84-a7ac-b97c733f513c
-- title:
--   SNumbers: to Real pos of ne top
-- statement:
--   A finite exponent `p` with `1 ≤ p` has `0 < p.toReal`. The `Fact (1 ≤ p)`
--   instance is how `PiLp` carries the admissibility of the exponent, so this is the
--   standard way to enter the `rpow` computations.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L53-L54
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L53-L54

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}

theorem SNumbers.toReal_pos_of_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : 0 < p.toReal := by sorry
