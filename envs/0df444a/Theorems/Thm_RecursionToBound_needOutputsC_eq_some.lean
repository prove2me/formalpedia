-- Prove2me | Theorems.Thm_RecursionToBound_needOutputsC_eq_some
-- name    : RecursionToBound.needOutputsC_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:55:28.194715+00:00
-- url     : https://prove2.me/theorems/cd68e2a6-6c2b-4493-950b-547d47e83a54
-- title:
--   Recursion To Bound: need Outputs C eq some
-- statement:
--   The maximum over Δ computed under a bound, if there is one, is the maximum over Δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L76-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L76-L82

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

theorem RecursionToBound.needOutputsC_eq_some (hS : S.Poly) {b : U} {k : ℕ} {r : ℕ × ℕ} {i : Idx} {n w : ℕ} (h : needOutputsC S b k r i n = some w) : w = needOutputs S k r i n := by sorry
