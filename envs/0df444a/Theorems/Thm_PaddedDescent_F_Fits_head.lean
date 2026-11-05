-- Prove2me | Theorems.Thm_PaddedDescent_F_Fits_head
-- name    : PaddedDescent.F.Fits.head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:34:42.403303+00:00
-- url     : https://prove2.me/theorems/acb942f3-50e8-4b29-8526-245954e63a33
-- title:
--   Fits: head
-- statement:
--   The current work list fits under the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Descend.lean#L49-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Descend.lean#L49-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_F_Descend
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork Groundwork.Prog Finset Lists
open Descend

theorem PaddedDescent.F.Fits.head {F : ℕ} : ∀ {sched : List Lvl} {Kup Λ B cnt : ℕ}, Fits F Kup Λ B cnt sched → cnt * instLen Kup Λ B + 2 ≤ F
  := by sorry
