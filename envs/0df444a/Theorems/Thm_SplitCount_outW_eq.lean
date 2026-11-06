-- Prove2me | Theorems.Thm_SplitCount_outW_eq
-- name    : SplitCount.outW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:00.167628+00:00
-- url     : https://prove2.me/theorems/b8698e12-0024-4a99-9fb1-b56a26177644
-- title:
--   Split Count: out W eq
-- statement:
--   The output function of the machine writes the word of the statement: v in n + 1 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L100-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L100-L101

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_CountKSat_CountTop_outW_eq

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.outW_eq (n : ℕ) (ψ : Fml) (v : ℕ) : outW ((List.replicate n (), ψ), v) = SatK.binary n v := by sorry
