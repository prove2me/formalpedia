-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Lseq_mono
-- name    : PaddedDescent.F.Arith.Lseq_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:07.669283+00:00
-- url     : https://prove2.me/theorems/222ff8d9-c432-443b-9627-cbca3c022b42
-- title:
--   Arith: Lseq mono
-- statement:
--   L_j grows with j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L34-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L34-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
import Definitions.Def_PaddedDescent_F_ArithSched
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
open PaddedDescent.F.Arith

theorem PaddedDescent.F.Arith.Lseq_mono {i j : ℕ} (h : i ≤ j) : Lseq i ≤ Lseq j := by sorry
