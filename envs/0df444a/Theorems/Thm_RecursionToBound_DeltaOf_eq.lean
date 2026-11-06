-- Prove2me | Theorems.Thm_RecursionToBound_DeltaOf_eq
-- name    : RecursionToBound.DeltaOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:12:42.170625+00:00
-- url     : https://prove2.me/theorems/6bdd4064-6c7f-4e3f-910e-a19734c81e74
-- title:
--   Recursion To Bound: Delta Of eq
-- statement:
--   The Δ of a formula as the maximum of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L130-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean#L130-L131

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Cert_Numbers
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma

theorem RecursionToBound.DeltaOf_eq (n : ℕ) (Φ : Groundwork.Sparsify.PFml) : SparsificationLemma.StepSparsify.DeltaOf n Φ = max 2 (((List.range n).map (occN Φ)).foldr max 0) := by sorry
