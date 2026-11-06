-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_entry_eq_or_mem
-- name    : QueryMachines.Bridge.Proof.entry_eq_or_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:17:45.15746+00:00
-- url     : https://prove2.me/theorems/d0cd5a2c-d255-4e2c-b626-61ef3439bc7c
-- title:
--   Proof: entry eq or mem
-- statement:
--   An entry is 0 or stands in the tables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L58-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L58-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed

theorem QueryMachines.Bridge.Proof.entry_eq_or_mem (T : Tab) (x : TableQuery) : entry T x = 0 ∨ ∃ r ∈ T, entry T x ∈ r := by sorry
