-- Prove2me | Theorems.Thm_SplitSat_decides_of_decidesW
-- name    : SplitSat.decides_of_decidesW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:30:19.855045+00:00
-- url     : https://prove2.me/theorems/2b4ebb72-ac4b-47e7-8207-4789c893b2a4
-- title:
--   Split Sat: decides of decides W
-- statement:
--   A machine that decides k-SAT on (n in unary, formula), in the sense of `DecidesW k`, decides
--   k-SAT on codes, in the sense of `Eight.ViaGrouping.Decides`, when the reader `decU k` is put in
--   front of it; the exponent and the constant stay.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Reader.lean#L31-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Reader.lean#L31-L43

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

theorem SplitSat.decides_of_decidesW {k : ℕ} (hk : 1 ≤ k) {M : StepMachine (List Unit × Fml) Bool} {δ : ℝ} {c : ℕ} (h : DecidesW k M δ c) :
    Decides (Stepped.mapIn (decU k) M) k δ c := by sorry
