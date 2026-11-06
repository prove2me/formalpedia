-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_size_le_len_tab
-- name    : QueryMachines.Bridge.Proof.size_le_len_tab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:21.225719+00:00
-- url     : https://prove2.me/theorems/a64f65e7-a920-4b2c-8444-ef05029a7f71
-- title:
--   Proof: size le len tab
-- statement:
--   The size of tables is at most the length of their word. (`Carried` is the inequality in the
--   other direction.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L81-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Tables.lean#L81-L82

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

theorem QueryMachines.Bridge.Proof.size_le_len_tab (T : Tab) : size T ≤ len T := by sorry
