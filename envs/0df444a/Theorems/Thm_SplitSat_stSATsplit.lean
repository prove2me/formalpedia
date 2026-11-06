-- Prove2me | Theorems.Thm_SplitSat_stSATsplit
-- name    : SplitSat.stSATsplit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:17.825859+00:00
-- url     : https://prove2.me/theorems/be28a723-f03e-48cc-b4a2-ed10584c6c04
-- title:
--   Split Sat: st SATsplit
-- statement:
--   **k-SAT with the machine named**: for every k ≥ 3 and δ > 0 there are τ, ℓ₃, τ₃ such that
--   `SATsplit k τ ℓ₃ τ₃`, the reduction run on the machine of Theorem 2 in its decision form without its
--   reader, has polynomial-time steps and decides k-SAT with the exponent δ. This is the statement
--   `SplitSat.StSATsplit`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L84-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L84-L87

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

theorem SplitSat.stSATsplit : StSATsplit := by sorry
