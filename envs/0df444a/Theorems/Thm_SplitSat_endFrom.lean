-- Prove2me | Theorems.Thm_SplitSat_endFrom
-- name    : SplitSat.endFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:03:21.840141+00:00
-- url     : https://prove2.me/theorems/cb04c388-e85d-4d51-8c6f-f5f018aff130
-- title:
--   Split Sat: end From
-- statement:
--   **Corollary 5 from the two tied statements**, which are hypotheses here: «s_k = 0 for every k ≥ 3.
--   Hence s_∞ = 0, and both ETH and SETH are false.» At k = 3 the Turing machine is that of
--   `StTiedThreeTM` («Theorem 2 gives s_3 = 0»), at k > 3 that of `StTiedTM` (the reduction); then the
--   general `SatK.sTM_eq_zero_of`. Nothing else is known of the machines.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L117-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L117-L139

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

theorem SplitSat.endFrom : StTiedTM → StTiedThreeTM → ThreeSatStatement := by sorry
