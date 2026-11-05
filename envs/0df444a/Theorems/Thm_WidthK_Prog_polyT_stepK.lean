-- Prove2me | Theorems.Thm_WidthK_Prog_polyT_stepK
-- name    : WidthK.Prog.polyT_stepK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:34:47.760195+00:00
-- url     : https://prove2.me/theorems/001a53f5-e0dc-42a7-8067-e61376dcb7e7
-- title:
--   Prog: poly T step K
-- statement:
--   The two children of a node of the sparsification tree are computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L62-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L62-L63

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

theorem WidthK.Prog.polyT_stepK (θ : ℕ → ℕ) (k : ℕ) {s : α → PFml} (hs : PolyT s) : PolyT fun x => stepK θ k (s x) := by sorry
