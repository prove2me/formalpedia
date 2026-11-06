-- Prove2me | Theorems.Thm_Suffices_stSuffices
-- name    : Suffices.stSuffices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:36:15.9881+00:00
-- url     : https://prove2.me/theorems/9c8e6202-7a84-417d-8e59-149f7d47f0fb
-- title:
--   Suffices: st Suffices
-- statement:
--   **By Lemma 4 with ε = δ/3, it suffices to decide whether a 3-CNF Φ with m ≤ Mn clauses is
--   satisfiable, in time O(2^{δ'm}) plus a polynomial in n (the deciding form of the paper's sentence,
--   which counts)** (proof of Theorem 2), for every enumeration for ε = δ/3: its constant M, and lines 1
--   to 4 of Algorithm 1 with its parameter τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Main.lean#L139-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Main.lean#L139-L139

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

theorem Suffices.stSuffices : StSuffices := by sorry
