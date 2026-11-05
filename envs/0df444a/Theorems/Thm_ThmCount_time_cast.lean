-- Prove2me | Theorems.Thm_ThmCount_time_cast
-- name    : ThmCount.time_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:41:38.627209+00:00
-- url     : https://prove2.me/theorems/e0acb039-bd92-45ab-ab65-9b64f9191513
-- title:
--   Thm Count: time cast
-- statement:
--   The time of `wrapper_counts` is at most the same expression with 2^{C·expN 3 (n+4)} in the place
--   of its floor, as a real number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Main.lean#L55-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Main.lean#L55-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_FrontEnd
import Definitions.Def_ThmCount_Rates
import Definitions.Def_Wrap_Main
import Mathlib.Tactic
import Definitions.Def_ThmCount_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d

set_option autoImplicit false
section
section
open ThmCount
open Turing Groundwork PaperSentences

theorem ThmCount.time_cast (C q a d n : ℕ) : ((q * (MainTheoremForms.timeN C 3 (n + 4) + a * (n + 2) ^ d + 1) ^ q : ℕ) : ℝ) ≤
    (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q := by sorry
