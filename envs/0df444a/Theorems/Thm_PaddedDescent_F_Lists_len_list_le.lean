-- Prove2me | Theorems.Thm_PaddedDescent_F_Lists_len_list_le
-- name    : PaddedDescent.F.Lists.len_list_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:26.272132+00:00
-- url     : https://prove2.me/theorems/b11e8254-a1b8-49cb-a3db-034e7b3c797f
-- title:
--   Lists: len list le
-- statement:
--   A list of k values, each with a word of length at most c − 2, has a word of length at most k·c + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L23-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L23-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_LenList
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Lists
open Groundwork

theorem PaddedDescent.F.Lists.len_list_le {α : Type} [Enc α] (w : List α) (c : ℕ) (h : ∀ a ∈ w, len a + 2 ≤ c) : len w ≤ w.length * c + 2 := by sorry
