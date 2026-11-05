-- Prove2me | Theorems.Thm_P2M_Eight_bxor_eq_iff_zero__40e241d4e138
-- name    : P2M_Eight_bxor_eq_iff_zero__40e241d4e138
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:26.791765+00:00
-- url     : https://prove2.me/theorems/a32b80c6-e485-421d-8ca6-2d71b0784353
-- title:
--   P2 M Eight bxor eq iff zero  40e241d4e138: P2 M Eight bxor eq iff zero  40e241d4e138
-- statement:
--   «Both brackets say x ⊕ y ⊕ u ⊕ v = 000»: x ⊕ u = v ⊕ y says this too.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L46-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L46-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
set_option autoImplicit false
section
section
open Eight
open Finset

theorem P2M_Eight_bxor_eq_iff_zero__40e241d4e138 (x y u v : Block) : bxor x u = bxor v y ↔ bxor (bxor x y) (bxor u v) = (false, false, false) := by sorry

alias «Eight».«bxor_eq_iff_zero'» := P2M_Eight_bxor_eq_iff_zero__40e241d4e138
