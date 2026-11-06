-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_size_entry_le
-- name    : QueryMachines.Bridge.Proof.size_entry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:48.875498+00:00
-- url     : https://prove2.me/theorems/7dcdce46-ab41-46e5-b16a-4793a0ed0d8c
-- title:
--   Proof: size entry le
-- statement:
--   An entry is no larger than the tables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L85-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L85-L97

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

theorem QueryMachines.Bridge.Proof.size_entry_le (T : Tab) (x : TableQuery) : size (entry T x) ≤ size T := by sorry
