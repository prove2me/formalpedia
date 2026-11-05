-- Prove2me | Theorems.Thm_PaddedDescent_kseq_strictMono__cf83c2
-- name    : PaddedDescent.kseq_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:28.607667+00:00
-- url     : https://prove2.me/theorems/cf83c2c4-b0a0-4086-846b-b302f2121372
-- title:
--   Padded Descent: kseq strict Mono
-- statement:
--   k_j grows strictly with j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L44-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
set_option autoImplicit false
section
section
open PaddedDescent

theorem PaddedDescent.kseq_strictMono : StrictMono kseq := by sorry
