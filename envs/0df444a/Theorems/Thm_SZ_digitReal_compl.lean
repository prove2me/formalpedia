-- Prove2me | Theorems.Thm_SZ_digitReal_compl
-- name    : SZ.digitReal_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:03.271508+00:00
-- url     : https://prove2.me/theorems/2e0af0c3-086d-4183-9795-cf93ef3c2fdc
-- title:
--   SZ: digit Real compl
-- statement:
--   The digitwise complement `dᵢ ↦ (m-1) - dᵢ` realises `1 - digitReal m d`.  At `m = 3`
--   this is the involution `a ↦ 2 - a` of the even-digit Cantor set that turns the difference
--   equation `x - √m y = v` of plan §1.2 into the sum equation `x + √m y'' = σ`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L248-L282
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L248-L282

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}

theorem SZ.digitReal_compl (h : IsDigits m d) :
    digitReal m (fun i => (m : ℤ) - 1 - d i) = 1 - digitReal m d := by sorry
