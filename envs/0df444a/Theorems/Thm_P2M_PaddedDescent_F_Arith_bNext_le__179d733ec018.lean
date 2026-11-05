-- Prove2me | Theorems.Thm_P2M_PaddedDescent_F_Arith_bNext_le__179d733ec018
-- name    : P2M_PaddedDescent_F_Arith_bNext_le__179d733ec018
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:17.035995+00:00
-- url     : https://prove2.me/theorems/d632621b-5ce0-45f1-83ff-f9b89ca0c9ad
-- title:
--   P2 M Padded Descent F Arith b Next le  179d733ec018: P2 M Padded Descent F Arith b Next le  179d733ec018
-- statement:
--   A weaker form of `bNext_le`: 6g³B + 8g⁴Λ instead of g³B + 2g⁴Λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L100-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L100-L103

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

theorem P2M_PaddedDescent_F_Arith_bNext_le__179d733ec018 {K g : ℕ} (hK : 256 ≤ K) (hg : K ≤ g) (lam B : ℕ) :
    bNext K g lam B ≤ 6 * (g ^ 3 * B) + 8 * (g ^ 4 * lam) := by sorry

alias «PaddedDescent».«F».«Arith».«bNext_le'» := P2M_PaddedDescent_F_Arith_bNext_le__179d733ec018
