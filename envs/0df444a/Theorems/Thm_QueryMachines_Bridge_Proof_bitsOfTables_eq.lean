-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_bitsOfTables_eq
-- name    : QueryMachines.Bridge.Proof.bitsOfTables_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:24.160766+00:00
-- url     : https://prove2.me/theorems/37886a6c-f57e-41a5-8fda-61cff2117795
-- title:
--   Proof: bits Of Tables eq
-- statement:
--   The largest number with the start value 1 is the largest number, with the start value 0, of the
--   list with 1 put behind it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L109-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L109-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed

theorem QueryMachines.Bridge.Proof.bitsOfTables_eq (T : Tab) : bitsOfTables T = ((T.flatten.map fun z : ℤ => z.natAbs.size) ++ [1]).foldr max 0 := by sorry
