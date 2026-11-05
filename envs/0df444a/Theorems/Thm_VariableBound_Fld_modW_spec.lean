-- Prove2me | Theorems.Thm_VariableBound_Fld_modW_spec
-- name    : VariableBound.Fld.modW_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:40:25.853872+00:00
-- url     : https://prove2.me/theorems/a67b181d-93fb-49f8-9c34-335e3fd82459
-- title:
--   Fld: mod W spec
-- statement:
--   For s ≥ 1 the search succeeds: `modW s` is a word of s bits, and X^s + `modW s` is irreducible.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L78-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Search.lean#L78-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial

theorem VariableBound.Fld.modW_spec {s : ℕ} (hs : 1 ≤ s) : (modW s).length = s ∧ Irreducible (modP (modW s)) := by sorry
