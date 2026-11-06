-- Prove2me | Theorems.Thm_VariableBound_Count_mod_two_pow_polyT
-- name    : VariableBound.Count.mod_two_pow_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:04:46.847714+00:00
-- url     : https://prove2.me/theorems/fb2a1081-d7a0-44f8-9150-d8cc2ab165b4
-- title:
--   Count: mod two pow poly T
-- statement:
--   The remainder of an integer modulo a power of 2 is polynomial-time, for the exponent in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Cert.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Cert.lean#L61-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net
variable {α : Type} [Enc α]

theorem VariableBound.Count.mod_two_pow_polyT {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => a x % 2 ^ k x := by sorry
