-- Prove2me | Theorems.Thm_SplitSat_stTiedThreeTM
-- name    : SplitSat.stTiedThreeTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:02.90824+00:00
-- url     : https://prove2.me/theorems/10efb0a4-7048-4b18-8ee4-c9b7a2d89427
-- title:
--   Split Sat: st Tied Three TM
-- statement:
--   **«Theorem 2 gives s_3 = 0», tied to the machine of Theorem 2 in its decision form**: for every
--   δ > 0 there are ℓ, τ such that `ThreeSatPrinted.SATCp ℓ τ` itself has polynomial-time steps and
--   decides 3-SAT with the exponent δ, a Turing machine M with finite alphabets simulates it with
--   polynomial overhead, and M decides 3-SAT within ⌊c·2^{δn}⌋ steps. This is the statement
--   `SplitSat.StTiedThreeTM`; ℓ and τ are those that `ThreeSatPrinted.algPseudocode_decides_viaC` gives
--   for δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L106-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L106-L111

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

theorem SplitSat.stTiedThreeTM : StTiedThreeTM := by sorry
