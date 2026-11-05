-- Prove2me | Theorems.Thm_VariableBound_Rename_card_not_occurs
-- name    : VariableBound.Rename.card_not_occurs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:15.044573+00:00
-- url     : https://prove2.me/theorems/534e3c60-4a28-44ff-92b7-da5f61de869b
-- title:
--   Rename: card not occurs
-- statement:
--   The number of variables that do not occur.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L188-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L188-L190

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_VariableBound_Paper_Rename_Math
set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
variable {N : ℕ} (φ : CNF N)

theorem VariableBound.Rename.card_not_occurs : Nat.card {i : Fin N // ¬ Occurs φ i} = N - numOcc φ := by sorry
