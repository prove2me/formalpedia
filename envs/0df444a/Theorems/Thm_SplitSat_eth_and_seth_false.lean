-- Prove2me | Theorems.Thm_SplitSat_eth_and_seth_false
-- name    : SplitSat.eth_and_seth_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:03:20.213335+00:00
-- url     : https://prove2.me/theorems/fd0c952b-2153-40aa-98dd-70d16cc8950a
-- title:
--   Split Sat: eth and seth false
-- statement:
--   **Corollary 5**: «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false.» The
--   statement is `PaperSentences.CorEth` of PaperSentencesStatement.lean. It is `endFrom` applied to
--   `stTiedTM` (the cited reduction of k-SAT to 3-SAT) and `stTiedThreeTM` (Theorem 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L144-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L144-L144

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

theorem SplitSat.eth_and_seth_false : ThreeSatStatement := by sorry
