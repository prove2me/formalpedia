-- Prove2me | Theorems.Thm_RecursionToBound_needAtC_eq_some
-- name    : RecursionToBound.needAtC_eq_some
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:00.487193+00:00
-- url     : https://prove2.me/theorems/7d2b185b-2788-46a0-83c9-536944fc87aa
-- title:
--   Recursion To Bound: need At C eq some
-- statement:
--   The exponent for one Δ computed under a bound, if there is one, is the exponent for this Δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L61-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L61-L65

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

theorem RecursionToBound.needAtC_eq_some (hS : S.Poly) {b : U} {k : ℕ} {i : Idx} {n Δ w : ℕ} (h : needAtC S b k i n Δ = some w) : w = needAt S k i n Δ := by sorry
