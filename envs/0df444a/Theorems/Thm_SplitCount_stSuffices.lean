-- Prove2me | Theorems.Thm_SplitCount_stSuffices
-- name    : SplitCount.stSuffices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:52:15.789394+00:00
-- url     : https://prove2.me/theorems/05ada21c-2e2a-4aad-8a5f-47028fa2d710
-- title:
--   Split Count: st Suffices
-- statement:
--   **«By the work of Dell et al. … this case suffices», for every procedure D that counts the
--   satisfying assignments of a 3-CNF as `CountsThree` says.** Under the hypotheses of `StSuffices`,
--   `engineBy step D` serves as the procedure for #k-SAT with the exponent δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Suffices.lean#L142-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Suffices.lean#L142-L166

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Leaf
import Definitions.Def_CountKSat_Walk
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Suffices
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify Paper CountKSat Eight Eight.Width Occ

theorem SplitCount.stSuffices : StSuffices := by sorry
