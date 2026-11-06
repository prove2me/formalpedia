-- Prove2me | Theorems.Thm_PairsToBound_clauseCountPow_of_two_le
-- name    : PairsToBound.clauseCountPow_of_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:49.969346+00:00
-- url     : https://prove2.me/theorems/44cbdfdc-1f09-4783-a2b1-25a5ba75a9e9
-- title:
--   Pairs To Bound: clause Count Pow of two le
-- statement:
--   (2n+1)^k ≤ n^(3k) for n ≥ 2: for n ≥ 3 by the printed (2n+1)^k ≤ n^(2k), for n = 2 because 5 ≤
--   2³.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L90-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L90-L95

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

theorem PairsToBound.clauseCountPow_of_two_le (k : ℕ) {n : ℕ} (hn : 2 ≤ n) : (2 * n + 1) ^ k ≤ n ^ (3 * k) := by sorry
