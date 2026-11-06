-- Prove2me | Theorems.Thm_RecursionToBound_lt_needNet_of_none
-- name    : RecursionToBound.lt_needNet_of_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:24.267838+00:00
-- url     : https://prove2.me/theorems/ea201ccd-daf0-4ba6-8032-d674ff5088ae
-- title:
--   Recursion To Bound: lt need Net of none
-- statement:
--   If the exponent of the networks computed under a bound is missing, the exponent of the networks
--   exceeds the bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L51-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L51-L58

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

theorem RecursionToBound.lt_needNet_of_none (hS : S.Poly) {b : U} {i : Idx} {Ub P B : ℕ} (h : needNetC S b i Ub P B = none) : b.length < needNet S i Ub P B := by sorry
