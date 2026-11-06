-- Prove2me | Theorems.Thm_RecursionToBound_lt_needAt_of_none
-- name    : RecursionToBound.lt_needAt_of_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:44.967834+00:00
-- url     : https://prove2.me/theorems/61526de7-1236-4c13-908c-cb30a135ac53
-- title:
--   Recursion To Bound: lt need At of none
-- statement:
--   If the exponent for one Δ computed under a bound is missing, the exponent for this Δ exceeds the
--   bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L69-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L69-L73

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

theorem RecursionToBound.lt_needAt_of_none (hS : S.Poly) {b : U} {k : ℕ} {i : Idx} {n Δ : ℕ} (h : needAtC S b k i n Δ = none) : b.length < needAt S k i n Δ := by sorry
