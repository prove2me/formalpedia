-- Prove2me | Theorems.Thm_P2M_Groundwork_Sparsify_polyT_greedyP__a113a83293ad
-- name    : P2M_Groundwork_Sparsify_polyT_greedyP__a113a83293ad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:14:27.880583+00:00
-- url     : https://prove2.me/theorems/f99c3704-a6de-4636-8389-1814fa03b824
-- title:
--   P2 M Groundwork Sparsify poly T greedy P  a113a83293ad: P2 M Groundwork Sparsify poly T greedy P  a113a83293ad
-- statement:
--   `greedyP k`, which picks at most k clauses of l that share no literal with `used` or with one
--   another, is
--   polynomial-time for every fixed k: the number of rounds is a constant of the machine. The induction
--   on k needs all
--   contexts α at once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L53-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Sparsify.lean#L53-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Sparsify
set_option autoImplicit false
section
section
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]

theorem P2M_Groundwork_Sparsify_polyT_greedyP__a113a83293ad (k : ℕ) : ∀ {α : Type} [Enc α] {used : α → PCl} {l : α → PFml}, PolyT used → PolyT l →
    PolyT fun x => greedyP k (used x) (l x) := by sorry

alias «Groundwork».«Sparsify».«polyT_greedyP'» := P2M_Groundwork_Sparsify_polyT_greedyP__a113a83293ad
