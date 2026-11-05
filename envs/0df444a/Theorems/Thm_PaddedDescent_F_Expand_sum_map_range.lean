-- Prove2me | Theorems.Thm_PaddedDescent_F_Expand_sum_map_range
-- name    : PaddedDescent.F.Expand.sum_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:07.056193+00:00
-- url     : https://prove2.me/theorems/09426b36-c1ea-4389-8835-da78b1216f3c
-- title:
--   Expand: sum map range
-- statement:
--   The Expand construction uses the sum map range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Expand.lean#L23-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Expand.lean#L23-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_PaddedDescent_F_Expand
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Stepped_sum_map_range
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Expand
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Expand.sum_map_range (f : ℕ → ℤ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by sorry
