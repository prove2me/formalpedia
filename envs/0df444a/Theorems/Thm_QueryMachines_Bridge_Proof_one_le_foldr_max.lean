-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_one_le_foldr_max
-- name    : QueryMachines.Bridge.Proof.one_le_foldr_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:07.416193+00:00
-- url     : https://prove2.me/theorems/3e037c83-6313-4fe4-aa39-17c8b9c77ecf
-- title:
--   Proof: one le foldr max
-- statement:
--   The largest number of a list, at least 1, is at least 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L29-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L29-L32

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

theorem QueryMachines.Bridge.Proof.one_le_foldr_max (l : List ℕ) : 1 ≤ l.foldr max 1 := by sorry
