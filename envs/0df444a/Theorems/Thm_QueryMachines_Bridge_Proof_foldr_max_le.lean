-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_foldr_max_le
-- name    : QueryMachines.Bridge.Proof.foldr_max_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:17:17.145317+00:00
-- url     : https://prove2.me/theorems/27858702-ee84-4526-98e3-abe68588f900
-- title:
--   Proof: foldr max le
-- statement:
--   It is at most every c ≥ 1 that bounds the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L44-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L44-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_Groundwork_Prog_NetE_foldr_max_le

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed

theorem QueryMachines.Bridge.Proof.foldr_max_le {l : List ℕ} {c : ℕ} (hc : 1 ≤ c) (h : ∀ x ∈ l, x ≤ c) : l.foldr max 1 ≤ c := by sorry
