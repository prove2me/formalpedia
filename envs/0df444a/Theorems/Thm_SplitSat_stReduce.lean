-- Prove2me | Theorems.Thm_SplitSat_stReduce
-- name    : SplitSat.stReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:54:11.719587+00:00
-- url     : https://prove2.me/theorems/b4b8f2aa-8965-4540-a862-467d9a9c4de9
-- title:
--   Split Sat: st Reduce
-- statement:
--   The reduction with the reader of the input in front decides k-SAT with the exponent δ, for every
--   procedure D: the statement `SplitSat.StReduce`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Reader.lean#L47-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Reader.lean#L47-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Walk
import Definitions.Def_CountKSat_InOut
import Definitions.Def_SplitSat_Reader
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping

theorem SplitSat.stReduce : StReduce := by sorry
