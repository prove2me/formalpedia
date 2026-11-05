-- Prove2me | Theorems.Thm_VariableBound_Rename_poly_mono
-- name    : VariableBound.Rename.poly_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:49.453752+00:00
-- url     : https://prove2.me/theorems/1dc15a66-cc43-4e32-8334-dd468e586297
-- title:
--   Rename: poly mono
-- statement:
--   C·a^C grows with C, for a ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Time.lean#L43-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Time.lean#L43-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Paper_Rename_Time
set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename

theorem VariableBound.Rename.poly_mono {C C' a : ℕ} (h : C ≤ C') (ha : 1 ≤ a) : C * a ^ C ≤ C' * a ^ C' := by sorry
