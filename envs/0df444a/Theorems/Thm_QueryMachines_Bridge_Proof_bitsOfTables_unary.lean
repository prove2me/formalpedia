-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_bitsOfTables_unary
-- name    : QueryMachines.Bridge.Proof.bitsOfTables_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:45.220845+00:00
-- url     : https://prove2.me/theorems/f9bce68b-e199-4899-a5a4-12f0dafaa19c
-- title:
--   Proof: bits Of Tables unary
-- statement:
--   The number of bits of the entries, in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L137-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L137-L137

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

theorem QueryMachines.Bridge.Proof.bitsOfTables_unary : Unary bitsOfTables := by sorry
