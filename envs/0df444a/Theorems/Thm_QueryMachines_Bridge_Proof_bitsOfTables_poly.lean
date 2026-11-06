-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_bitsOfTables_poly
-- name    : QueryMachines.Bridge.Proof.bitsOfTables_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:46.644993+00:00
-- url     : https://prove2.me/theorems/15349ae2-b3d2-4480-bd47-687fcb3b8b45
-- title:
--   Proof: bits Of Tables poly
-- statement:
--   The number of bits of the entries is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L112-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L112-L113

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

theorem QueryMachines.Bridge.Proof.bitsOfTables_poly : PolyT bitsOfTables := by sorry
