-- Prove2me | Theorems.Thm_VariableBound_Net_Ev_emod_eq_of_modEq
-- name    : VariableBound.Net.Ev.emod_eq_of_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:48:36.178405+00:00
-- url     : https://prove2.me/theorems/132fc17f-2bc1-4389-9dc4-c428f78407d9
-- title:
--   Ev: emod eq of mod Eq
-- statement:
--   A number in [0, N) is the remainder modulo N of every number congruent to it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Ev.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Ev.lean#L61-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_Ev
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Ev
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
open ClauseBound.ParityChecks (Vof)

theorem VariableBound.Net.Ev.emod_eq_of_modEq {a b N : ℤ} (h : a ≡ b [ZMOD N]) (h0 : 0 ≤ a) (h1 : a < N) : b % N = a := by sorry
