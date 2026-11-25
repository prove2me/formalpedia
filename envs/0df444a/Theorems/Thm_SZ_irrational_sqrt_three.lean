-- Prove2me | Theorems.Thm_SZ_irrational_sqrt_three
-- name    : SZ.irrational_sqrt_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:06:51.896739+00:00
-- url     : https://prove2.me/theorems/6626ba1a-1c5d-5ec6-b2a3-c17a3f9902fd
-- title:
--   SZ: irrational sqrt three
-- statement:
--   The SZ construction uses the irrational sqrt three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L95-L97
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L95-L97

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.irrational_sqrt_three : Irrational (Real.sqrt 3) := by sorry
