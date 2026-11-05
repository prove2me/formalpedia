-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Zof_le_Qmof
-- name    : PaddedDescent.F.Arith.Zof_le_Qmof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:05.00921+00:00
-- url     : https://prove2.me/theorems/da1a46e6-cd08-4ff8-abfe-4f28c6fe6a41
-- title:
--   Arith: Zof le Qmof
-- statement:
--   Z ≤ Qm.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L162-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L162-L164

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

theorem PaddedDescent.F.Arith.Zof_le_Qmof (k s n : ℕ) : Zof s ≤ Qmof k s n := by sorry
