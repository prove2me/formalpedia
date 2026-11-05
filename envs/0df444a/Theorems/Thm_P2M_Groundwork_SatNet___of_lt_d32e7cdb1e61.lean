-- Prove2me | Theorems.Thm_P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61
-- name    : P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:36.921793+00:00
-- url     : https://prove2.me/theorems/ab09ce2c-da4a-4fb4-9cac-ce0f161cc5b6
-- title:
--   P2 M Groundwork Sat Net   of lt d32e7cdb1e61: P2 M Groundwork Sat Net   of lt d32e7cdb1e61
-- statement:
--   The interaction of clusters a < b is the product of the equalities between them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L291-L318
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SatNet.lean#L291-L318

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}

theorem P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61 {a b : Fin g} (h : a < b) (z z' : Sl μ k → Bool) :
    (net φ g μ k).Ψ a b z z' = if ∀ s s', Link φ (a, s) (b, s') → z s = z' s' then 1 else 0 := by sorry

alias «Groundwork».«SatNet».«Ψ_of_lt» := P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61
