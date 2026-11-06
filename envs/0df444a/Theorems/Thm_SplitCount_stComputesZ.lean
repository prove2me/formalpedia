-- Prove2me | Theorems.Thm_SplitCount_stComputesZ
-- name    : SplitCount.stComputesZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:51:00.813688+00:00
-- url     : https://prove2.me/theorems/fea502fb-2d4f-4efe-869e-350b22832042
-- title:
--   Split Count: st Computes Z
-- statement:
--   **The proof of Theorem 2, with K and g chosen from δ' as there, computes Z.** For 0 < δ' ≤ 1, K
--   ≥ 2 with K ≥ 72/δ', g = 3K⁸ and any algorithm E for cliques on K nodes with the exponent δ'/12, the
--   algorithm of the printed proof of Lemma 1 with E, run on the network of Φ on g clusters, computes Z
--   as Section 6 says.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/StepOne.lean#L89-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/StepOne.lean#L89-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_Occ_Main
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_StepOne
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ

theorem SplitCount.stComputesZ : StComputesZ := by sorry
