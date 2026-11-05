-- Prove2me | Theorems.Thm_WidthK_Prog_polyT_tryT
-- name    : WidthK.Prog.polyT_tryT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:35:07.168081+00:00
-- url     : https://prove2.me/theorems/516a9a7b-6012-4c7e-abd1-059397a78ade
-- title:
--   Prog: poly T try T
-- statement:
--   The search for a heart of a given size that reaches a given threshold is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L46-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
set_option autoImplicit false
section
section
open WidthK WidthK.Prog
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]

theorem WidthK.Prog.polyT_tryT (k : ℕ) {s : α → PFml} {c : α → (ℕ × ℕ) × ℕ} (hs : PolyT s) (hc : PolyT c) :
    PolyT fun x => tryT k (s x) (c x) := by sorry
