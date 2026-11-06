-- Prove2me | Theorems.Thm_PairsToBound_steps_le
-- name    : PairsToBound.steps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:00.877111+00:00
-- url     : https://prove2.me/theorems/4cb0b0ea-db63-427b-8cf5-2deead180637
-- title:
--   Pairs To Bound: steps le
-- statement:
--   If L + 1 ≤ n^(8k) and n ≥ 2, k ≥ 1, then q·(L + 2ⁿ + 1)^q ≤ 2^(8q·n)·n^(8q·k).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L137-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L137-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)

theorem PairsToBound.steps_le (q : ℕ) {k n L : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) (hL : L + 1 ≤ n ^ (8 * k)) : q * (L + 2 ^ n + 1) ^ q ≤ 2 ^ (8 * q * n) * n ^ (8 * q * k) := by sorry
