-- Prove2me | Theorems.Thm_P2M_PaddedDescent_F_Lists_len_list_le__7630c2814a7f
-- name    : P2M_PaddedDescent_F_Lists_len_list_le__7630c2814a7f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:23.313193+00:00
-- url     : https://prove2.me/theorems/8a275499-ae84-4848-9ae6-aa929dd6c00e
-- title:
--   P2 M Padded Descent F Lists len list le  7630c2814a7f: P2 M Padded Descent F Lists len list le  7630c2814a7f
-- statement:
--   The same when only a bound k on the number of members is known.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L33-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/LenList.lean#L33-L35

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

theorem P2M_PaddedDescent_F_Lists_len_list_le__7630c2814a7f {α : Type} [Enc α] (w : List α) {k : ℕ} (c : ℕ) (hk : w.length ≤ k) (h : ∀ a ∈ w, len a + 2 ≤ c) :
    len w ≤ k * c + 2 := by sorry

alias «PaddedDescent».«F».«Lists».«len_list_le'» := P2M_PaddedDescent_F_Lists_len_list_le__7630c2814a7f
