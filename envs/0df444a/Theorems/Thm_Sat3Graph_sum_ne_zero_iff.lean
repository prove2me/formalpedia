-- Prove2me | Theorems.Thm_Sat3Graph_sum_ne_zero_iff
-- name    : Sat3Graph.sum_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:26.656505+00:00
-- url     : https://prove2.me/theorems/e31eb754-9115-4beb-b8b3-86121d897779
-- title:
--   Sat3 Graph: sum ne zero iff
-- statement:
--   A sum of natural numbers is not 0 exactly if one of them is not 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Dominating.lean#L35-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Dominating.lean#L35-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Ask
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Dominating
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems Paper SizeCircuit SplitSat

theorem Sat3Graph.sum_ne_zero_iff {α : Type} (f : α → ℕ) : ∀ L : List α, (L.map f).sum ≠ 0 ↔ ∃ x ∈ L, f x ≠ 0
  := by sorry
