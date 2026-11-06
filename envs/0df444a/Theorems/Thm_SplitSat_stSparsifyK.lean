-- Prove2me | Theorems.Thm_SplitSat_stSparsifyK
-- name    : SplitSat.stSparsifyK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:22.549799+00:00
-- url     : https://prove2.me/theorems/93149cbe-5867-42c1-9f55-4ac65e55ebc3
-- title:
--   Split Sat: st Sparsify K
-- statement:
--   «sparsify»: for every k ≥ 3 and ε > 0 some threshold parameter τ makes the tree of the procedure
--   behind the Lean form of Lemma 4, run at width k, sparsify width k with at most 2^{εn} leaves. This
--   is the statement `SplitSat.StSparsifyK`, taken from
--   `SparsificationLemma.TreeWalk.lemSparsification_walk_k`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L50-L52

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

theorem SplitSat.stSparsifyK : StSparsifyK := by sorry
