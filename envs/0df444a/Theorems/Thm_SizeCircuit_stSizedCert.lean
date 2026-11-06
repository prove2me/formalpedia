-- Prove2me | Theorems.Thm_SizeCircuit_stSizedCert
-- name    : SizeCircuit.stSizedCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:37.790198+00:00
-- url     : https://prove2.me/theorems/d3fec702-4512-46b4-bd62-4e1bd42c6cf5
-- title:
--   Size Circuit: st Sized Cert
-- statement:
--   **`StSizedCert`.** The steps of `sizedBy gates E` are polynomial time if those of E are and the
--   circuits are computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/SizedCert.lean#L68-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/SizedCert.lean#L68-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_SizedCert
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

theorem SizeCircuit.stSizedCert : StSizedCert := by sorry
