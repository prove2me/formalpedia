-- Prove2me | Theorems.Thm_VariableBound_Rename_val_pos
-- name    : VariableBound.Rename.val_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:13:35.743757+00:00
-- url     : https://prove2.me/theorems/a592d674-4f84-4919-9300-8494d4978165
-- title:
--   Rename: val pos
-- statement:
--   The new name of a variable is its position in the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L89-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L89-L90

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
import Theorems.Thm_Groundwork_PolyT_idxOf
attribute [local fun_prop] Groundwork.PolyT.idxOf


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
variable {N : ℕ} (φ : CNF N)

theorem VariableBound.Rename.val_pos (i : {i : Fin N // Occurs φ i}) : (pos φ i).val = (occL (toN φ)).idxOf i.1.val := by sorry
