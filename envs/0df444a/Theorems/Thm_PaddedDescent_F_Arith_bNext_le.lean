-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_bNext_le
-- name    : PaddedDescent.F.Arith.bNext_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:13.301684+00:00
-- url     : https://prove2.me/theorems/ee03fdfe-4884-4c5b-ae5f-e60c94c1de47
-- title:
--   Arith: b Next le
-- statement:
--   The entries after one level have at most g³B + 2g⁴Λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L76-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L76-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.bNext_le {K g : ℕ} (hK : 256 ≤ K) (hg : K ≤ g) (lam B : ℕ) :
    bNext K g lam B ≤ g ^ 3 * B + 2 * (g ^ 4 * lam) := by sorry
