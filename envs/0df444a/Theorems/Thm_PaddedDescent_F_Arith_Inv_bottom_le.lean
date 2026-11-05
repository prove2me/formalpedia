-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Inv_bottom_le
-- name    : PaddedDescent.F.Arith.Inv.bottom_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:55.89321+00:00
-- url     : https://prove2.me/theorems/c8c969cc-518b-434b-ad00-e7c2561b49de
-- title:
--   Inv: bottom le
-- statement:
--   The brute force at the bottom: K₀(K₀−1)/2·Λ ≤ X + Z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L236-L242
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L236-L242

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}

theorem PaddedDescent.F.Arith.Inv.bottom_le (h : Inv t X Z Qm Wm L 0 lam B cnt) : Kseq 0 * (Kseq 0 - 1) / 2 * lam ≤ X + Z := by sorry
