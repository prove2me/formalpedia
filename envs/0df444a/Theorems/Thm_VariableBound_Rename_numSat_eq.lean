-- Prove2me | Theorems.Thm_VariableBound_Rename_numSat_eq
-- name    : VariableBound.Rename.numSat_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:39:38.104044+00:00
-- url     : https://prove2.me/theorems/12625e35-973f-4dd8-8b8d-4e2c72685f21
-- title:
--   Rename: num Sat eq
-- statement:
--   The sentence after Corollary 11: for a formula on N variables of which n occur, the number of
--   satisfying assignments of all N variables is 2^(N−n) times the number of satisfying assignments as
--   assignments of the n variables that occur.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L195-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L195-L207

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

theorem VariableBound.Rename.numSat_eq : SatK.numSat φ = 2 ^ (N - numOcc φ) * numSatOcc φ := by sorry
