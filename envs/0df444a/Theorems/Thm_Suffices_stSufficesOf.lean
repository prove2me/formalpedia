-- Prove2me | Theorems.Thm_Suffices_stSufficesOf
-- name    : Suffices.stSufficesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:35:30.59127+00:00
-- url     : https://prove2.me/theorems/ad49e2b3-5d41-45e6-9336-57ce943af89c
-- title:
--   Suffices: st Suffices Of
-- statement:
--   **By Lemma 4 with ε = δ/3, it suffices to decide whether a 3-CNF Φ with m ≤ Mn clauses is
--   satisfiable, in time O(2^{δ'm}) plus a polynomial in n (the deciding form of the paper's sentence,
--   which counts)** (proof of Theorem 2), from the run of the loop, the count of the total time and the
--   polynomial-time steps of the loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Main.lean#L41-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Main.lean#L41-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Loop
import Definitions.Def_Suffices_Total
import Definitions.Def_Exits_Poly
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Suffices_Main
set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits

theorem Suffices.stSufficesOf : StSufficesOf := by sorry
