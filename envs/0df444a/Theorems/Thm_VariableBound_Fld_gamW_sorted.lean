-- Prove2me | Theorems.Thm_VariableBound_Fld_gamW_sorted
-- name    : VariableBound.Fld.gamW_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:09.204378+00:00
-- url     : https://prove2.me/theorems/69d129b0-93ff-4a70-8007-be1f1bdc2033
-- title:
--   Fld: gam W sorted
-- statement:
--   Γ_u is listed in increasing order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L56-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Definitions.Def_VariableBound_Field_Transfer
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset

theorem VariableBound.Fld.gamW_sorted (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : (gamW m a g u).Pairwise (· < ·) := by sorry
