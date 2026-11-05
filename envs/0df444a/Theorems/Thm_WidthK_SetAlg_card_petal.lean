-- Prove2me | Theorems.Thm_WidthK_SetAlg_card_petal
-- name    : WidthK.SetAlg.card_petal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:52.270035+00:00
-- url     : https://prove2.me/theorems/cc99d75c-b22e-4207-9e03-ee578e53f2d1
-- title:
--   Set Alg: card petal
-- statement:
--   All petals have the same size, j - |H|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L63-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
set_option autoImplicit false
section
section
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]

theorem WidthK.SetAlg.card_petal {F : Finset (Finset α)} {j : ℕ} {H D : Finset α} (hD : D ∈ petals F j H) : D.card = j - H.card := by sorry
