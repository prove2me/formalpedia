-- Prove2me | Theorems.Thm_SizeCircuit_stForces
-- name    : SizeCircuit.stForces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:37:46.245165+00:00
-- url     : https://prove2.me/theorems/76247fa6-0a62-45f7-82a6-e97cb2230937
-- title:
--   Size Circuit: st Forces
-- statement:
--   **`StForces`.** «clauses of at most 3 literals that force it to equal the value of the gate»:
--   the four clauses of a gate hold exactly if the variable of its wire has the value of the gate, and
--   each has at most 3 literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L69-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L69-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.stForces : StForces := by sorry
