-- Prove2me | Theorems.Thm_RecursionToBound_lt_needOutputs_of_none
-- name    : RecursionToBound.lt_needOutputs_of_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:53.481634+00:00
-- url     : https://prove2.me/theorems/8d69aff0-14fa-4750-88e1-a5a1550da66a
-- title:
--   Recursion To Bound: lt need Outputs of none
-- statement:
--   If the maximum over Δ computed under a bound is missing, the maximum over Δ exceeds the bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L85-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L85-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}

theorem RecursionToBound.lt_needOutputs_of_none (hS : S.Poly) {b : U} {k : ℕ} {r : ℕ × ℕ} {i : Idx} {n : ℕ} (h : needOutputsC S b k r i n = none) : b.length < needOutputs S k r i n := by sorry
