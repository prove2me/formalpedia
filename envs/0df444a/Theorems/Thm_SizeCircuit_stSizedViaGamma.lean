-- Prove2me | Theorems.Thm_SizeCircuit_stSizedViaGamma
-- name    : SizeCircuit.stSizedViaGamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:34.360201+00:00
-- url     : https://prove2.me/theorems/ec75c866-aaa5-4ded-a1da-220146cb2595
-- title:
--   Size Circuit: st Sized Via Gamma
-- statement:
--   **`StSizedViaGamma`.** With the circuits `sizeGates`: from Corollary 6 for machines cut into
--   steps, the interface `GraphProblems.StSized` of proof/consequences/GraphProblems/; the machine is
--   `sizedBy sizeGates E`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Main.lean#L66-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Main.lean#L66-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_SizeCircuit_Sized
import Definitions.Def_SizeCircuit_SizedCert
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Main
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

theorem SizeCircuit.stSizedViaGamma : StSizedViaGamma := by sorry
