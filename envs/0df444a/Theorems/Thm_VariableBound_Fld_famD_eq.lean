-- Prove2me | Theorems.Thm_VariableBound_Fld_famD_eq
-- name    : VariableBound.Fld.famD_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:44.338051+00:00
-- url     : https://prove2.me/theorems/7e04d0ca-56d8-4423-b386-73a0ad5fd4b3
-- title:
--   Fld: fam D eq
-- statement:
--   The list of the family: first leave out the u with 2^a·|Γ_u| > 16m, then list the sets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L76-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Transfer.lean#L76-L79

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

theorem VariableBound.Fld.famD_eq (m a : ℕ) : famD m a =
    ((wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m)).filter fun u =>
      decide (2 ^ a * (gamW m a (modW (sD m)) u).length ≤ 16 * m)).map (gamW m a (modW (sD m))) := by sorry
