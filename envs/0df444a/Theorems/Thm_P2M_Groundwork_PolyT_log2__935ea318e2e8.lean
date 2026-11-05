-- Prove2me | Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
-- name    : P2M_Groundwork_PolyT_log2__935ea318e2e8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:09.821302+00:00
-- url     : https://prove2.me/theorems/3fd18757-b8bf-42ea-bfa6-07459f3fe23c
-- title:
--   P2 M Groundwork Poly T log2  935ea318e2e8: P2 M Groundwork Poly T log2  935ea318e2e8
-- statement:
--   The binary logarithm, rounded down: the number of binary digits minus 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L101-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L101-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1
import Definitions.Def_ToTuring_Lib_Nat1b
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem P2M_Groundwork_PolyT_log2__935ea318e2e8 {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => Nat.log2 (f x)) := by sorry

alias «Groundwork».«PolyT».«log2'» := P2M_Groundwork_PolyT_log2__935ea318e2e8
