-- Prove2me | Theorems.Thm_PaddedDescent_F_Lists_length_flatMap_le
-- name    : PaddedDescent.F.Lists.length_flatMap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:54.254642+00:00
-- url     : https://prove2.me/theorems/bfa3121d-7929-411e-991b-e1120ea87c24
-- title:
--   Lists: length flat Map le
-- statement:
--   If e a has at most c members for every member a of w, then w.flatMap e has at most (length of
--   w)·c members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L39-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L39-L47

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

theorem PaddedDescent.F.Lists.length_flatMap_le {α β : Type*} (w : List α) (e : α → List β) (c : ℕ) (h : ∀ a ∈ w, (e a).length ≤ c) :
    (w.flatMap e).length ≤ w.length * c := by sorry
