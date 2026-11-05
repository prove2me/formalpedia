-- Prove2me | Theorems.Thm_PaddedDescent_gseq_eq
-- name    : PaddedDescent.gseq_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:58.548121+00:00
-- url     : https://prove2.me/theorems/2659d633-bb84-464e-8188-82df43a6a93c
-- title:
--   Padded Descent: gseq eq
-- statement:
--   g_j = 2^(k_j + 47 + j).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L53-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L53-L54

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

theorem PaddedDescent.gseq_eq (j : ℕ) : gseq j = 2 ^ (kseq j + 47 + j) := by sorry
