-- Prove2me | Theorems.Thm_VariableBound_Rename_numSat_ren
-- name    : VariableBound.Rename.numSat_ren
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:58:37.442188+00:00
-- url     : https://prove2.me/theorems/edbed5f3-6690-46c1-bdfd-d6910c4f82db
-- title:
--   Rename: num Sat ren
-- statement:
--   The number of satisfying assignments of the renamed formula is the number of satisfying
--   assignments of φ, as assignments of the variables that occur.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L174-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L174-L178

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

theorem VariableBound.Rename.numSat_ren : SatK.numSat (ren φ) = numSatOcc φ := by sorry
