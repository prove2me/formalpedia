-- Prove2me | Theorems.Thm_Sat3Graph_colorF_polyT
-- name    : Sat3Graph.colorF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:23.406879+00:00
-- url     : https://prove2.me/theorems/b94b6b8b-3424-41b0-9612-8a5b18e2bf0e
-- title:
--   Sat3 Graph: color F poly T
-- statement:
--   The formula of the colorings is computed in polynomial time from (n in unary, matrix).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Cert.lean#L41-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Cert.lean#L41-L46

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat

theorem Sat3Graph.colorF_polyT (k : ℕ) : PolyT fun a : List Unit × List Bool => colorF k a.1.length a.2 := by sorry
