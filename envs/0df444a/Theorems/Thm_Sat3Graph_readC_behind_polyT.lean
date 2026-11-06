-- Prove2me | Theorems.Thm_Sat3Graph_readC_behind_polyT
-- name    : Sat3Graph.readC_behind_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:32.824593+00:00
-- url     : https://prove2.me/theorems/6797a6eb-a315-4c4a-a9cf-0cda5cae352e
-- title:
--   Sat3 Graph: read C behind poly T
-- statement:
--   Behind a polynomial-time reader r of (n in unary, matrix), the reader for colorings is
--   polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Cert.lean#L50-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Cert.lean#L50-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_SizedCert
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Walk
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Cert
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat

theorem Sat3Graph.readC_behind_polyT (k : ℕ) {r : List Bool → List Unit × List Bool} (hr : PolyT r) :
    PolyT fun x => (List.replicate ((r x).1.length * k) (), (colorF k (r x).1.length (r x).2).dedup) := by sorry
