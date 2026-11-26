-- Prove2me | Theorems.Thm_QuarterSumLadder_distinct
-- name    : QuarterSumLadder.distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:46.525209+00:00
-- url     : https://prove2.me/theorems/faf14ac7-3a72-434e-afee-ba90d46f604b
-- title:
--   Quarter Sum Ladder: distinct
-- statement:
--   The values `0, 1, i, -1, -i` are pairwise distinct (as `simp` lemmas).
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L72-L78
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean#L72-L78

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.distinct :
    ((1 : GaussianInt) = gi ↔ False) ∧ ((1 : GaussianInt) = -1 ↔ False) ∧
    ((1 : GaussianInt) = -gi ↔ False) ∧ (gi = 1 ↔ False) ∧ (gi = -1 ↔ False) ∧
    (gi = -gi ↔ False) ∧ ((-1 : GaussianInt) = 1 ↔ False) ∧ ((-1 : GaussianInt) = gi ↔ False) ∧
    ((-1 : GaussianInt) = -gi ↔ False) ∧ (-gi = 1 ↔ False) ∧ (-gi = gi ↔ False) ∧
    (-gi = (-1 : GaussianInt) ↔ False) := by sorry
