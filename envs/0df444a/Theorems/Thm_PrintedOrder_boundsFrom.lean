-- Prove2me | Theorems.Thm_PrintedOrder_boundsFrom
-- name    : PrintedOrder.boundsFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:17:16.256409+00:00
-- url     : https://prove2.me/theorems/5967758a-b7b6-4296-89c3-1c1ce8974412
-- title:
--   Printed Order: bounds From
-- statement:
--   **The bounds on the tree, without the sum**, from the sum at one step (`StStepAdds`), which is a
--   hypothesis: for every k and ε > 0 some threshold parameter τ gives a tree with at most 2^{εn}
--   leaves, O(n) clauses in each leaf and a short stack. The thresholds are those of
--   `WidthK.stExistsTau`; the bounds are those of `CountKSat.stProgC`, which gets the hypothesis for the
--   sum at one step and proof/consequences/CountKSat/'s own `stRootCount` and `stSumLeaves`;
--   `SplitCount.sparsifiesPlain_of` carries them to the tree whose side list starts empty; its sum over
--   the leaves is dropped.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Counting.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Counting.lean#L55-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_PrintedOrder_AddUp
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Counting
set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal

theorem PrintedOrder.boundsFrom : StStepAdds → StBounds := by sorry
