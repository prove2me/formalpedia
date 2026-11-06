-- Prove2me | Theorems.Thm_SplitSat_stTiedTM
-- name    : SplitSat.stTiedTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:03:32.727775+00:00
-- url     : https://prove2.me/theorems/b38a7a93-edb7-4b1c-8d8e-e00c14297f58
-- title:
--   Split Sat: st Tied TM
-- statement:
--   **Tied to the machine, on Mathlib's Turing machines**: for every k ≥ 3 and δ > 0 there are τ,
--   ℓ₃, τ₃ such that `SATsplit k τ ℓ₃ τ₃` itself has polynomial-time steps and decides k-SAT with the
--   exponent δ, a Turing machine M with finite alphabets simulates it with polynomial overhead, and M
--   decides k-SAT within ⌊c·2^{δn}⌋ steps. This is the statement `SplitSat.StTiedTM`. In the proof the
--   named machine has the exponent δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L94-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L94-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Reader
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_SplitSat_Main
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal

theorem SplitSat.stTiedTM : StTiedTM := by sorry
