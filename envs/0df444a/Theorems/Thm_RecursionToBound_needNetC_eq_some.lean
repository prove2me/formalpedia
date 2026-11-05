-- Prove2me | Theorems.Thm_RecursionToBound_needNetC_eq_some
-- name    : RecursionToBound.needNetC_eq_some
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:56:29.314208+00:00
-- url     : https://prove2.me/theorems/361512a9-435b-42c5-a6be-e5f63fed0ef7
-- title:
--   Recursion To Bound: need Net C eq some
-- statement:
--   The exponent of the networks computed under a bound, if there is one, is the exponent of the
--   networks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L43-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L43-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}

theorem RecursionToBound.needNetC_eq_some (hS : S.Poly) {b : U} {i : Idx} {Ub P B w : ℕ} (h : needNetC S b i Ub P B = some w) : w = needNet S i Ub P B := by sorry
