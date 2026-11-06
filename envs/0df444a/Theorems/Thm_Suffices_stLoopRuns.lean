-- Prove2me | Theorems.Thm_Suffices_stLoopRuns
-- name    : Suffices.stLoopRuns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:29:35.696464+00:00
-- url     : https://prove2.me/theorems/a0b9dcf3-6151-4790-9c7a-82575e549914
-- title:
--   Suffices: st Loop Runs
-- statement:
--   **The run of lines 1 to 4 of Algorithm 1**: «for each Φ in the list that Lemma 4 computes from φ
--   and ε do» (line 2), the test Count(Φ) > 0 in place of the paper's line 3, which counts; only the
--   formulas up to the first with a positive count are tested.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L99-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L99-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)

theorem Suffices.stLoopRuns : StLoopRuns := by sorry
