-- Prove2me | Theorems.Thm_SparsificationLemma_Shrink_card_heavy_le
-- name    : SparsificationLemma.Shrink.card_heavy_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:51:20.572259+00:00
-- url     : https://prove2.me/theorems/93630aaf-423e-4ae6-a880-de291eb3bb72
-- title:
--   Shrink: card heavy le
-- statement:
--   The second child has at most as many clauses as F.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Shrink.lean#L52-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Shrink.lean#L52-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_Shrink
import Theorems.Thm_WidthK_Node_heavy

set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain CountKSat
open SparsificationLemma.Shrink
variable {α : Type} [DecidableEq α] {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}

theorem SparsificationLemma.Shrink.card_heavy_le (hF : Reduced F) (h : Heart θ F j H) : (heavy F j H).card ≤ F.card := by sorry
