-- Prove2me | Theorems.Thm_SplitSat_exists_instance
-- name    : SplitSat.exists_instance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:33:16.875725+00:00
-- url     : https://prove2.me/theorems/8965017f-9af3-4fcd-8340-9ef07cb49347
-- title:
--   Split Sat: exists instance
-- statement:
--   A formula with numbers below n as variables, at most k literals per clause and no clause written
--   twice is `Decode.toN φ` for an instance φ of k-SAT on n variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L48-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L48-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_SplitSat_Leaf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Eight.Width GraphProblems

theorem SplitSat.exists_instance {k n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hnd : ψ.Nodup) :
    ∃ φ : Sat3.CNF n, SatK.IsKCNF k φ ∧ Decode.toN φ = ψ := by sorry
