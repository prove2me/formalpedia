-- Prove2me | Theorems.Thm_Sat3Graph_stCert
-- name    : Sat3Graph.stCert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:40.014106+00:00
-- url     : https://prove2.me/theorems/e0981c88-4722-4306-829b-2c3aa089557b
-- title:
--   Sat3 Graph: st Cert
-- statement:
--   **`StCert`.** The steps of the five deciders are polynomial time if those of D are and the
--   circuits are computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Main.lean#L40-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Main.lean#L40-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_Sat3Graph_Sets
import Definitions.Def_Sat3Graph_Dominating
import Definitions.Def_Sat3Graph_Coloring
import Definitions.Def_Sat3Graph_Cert
import Definitions.Def_Sat3Graph_Host
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_Complement_Readers
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_GraphProblems_DomTree
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Main
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement SplitSat

theorem Sat3Graph.stCert : StCert := by sorry
