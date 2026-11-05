-- Prove2me | Theorems.Thm_VariableBound_Fld_gamW_nodup
-- name    : VariableBound.Fld.gamW_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:32.376206+00:00
-- url     : https://prove2.me/theorems/186d297b-19d7-4bef-8c86-ee2df1eed501
-- title:
--   Fld: gam W nodup
-- statement:
--   Γ_u is listed without repetitions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L60-L61

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

theorem VariableBound.Fld.gamW_nodup (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : (gamW m a g u).Nodup := by sorry
