-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_gtop_le_Ytop
-- name    : PaddedDescent.F.Arith.gtop_le_Ytop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:21.749966+00:00
-- url     : https://prove2.me/theorems/39a98ca9-ee98-41fc-aae3-6e1a13f0d7de
-- title:
--   Arith: gtop le Ytop
-- statement:
--   `gtop` is at most its square Y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L46-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.gtop_le_Ytop (s : ℕ) : gtop s ≤ Ytop s := by sorry
