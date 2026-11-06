-- Prove2me | Theorems.Thm_PiecesCounted_answer_polyT
-- name    : PiecesCounted.answer_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:44.217665+00:00
-- url     : https://prove2.me/theorems/95710509-ffe6-4f8b-9f07-e251bced706f
-- title:
--   Pieces Counted: answer poly T
-- statement:
--   The shape of `answerOf`, for any polynomial-time parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Padded.lean#L46-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Padded.lean#L46-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_PadThen
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Padded
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.answer_polyT {dF : List Unit → ℕ} {rg : List Unit → List ℕ} {capF : Bool × List Unit × ℕ → ℕ} {sh : List Unit → ℤ} {top bot : PQ → ℤ} {val : AppRunningTime.ValQ → ℤ}
    (hd : PolyT dF) (hr : PolyT rg) (hc : PolyT capF) (hs : PolyT sh) (ht : PolyT top) (hb : PolyT bot) (hv : PolyT val) :
    PolyT fun x : (List Unit × Question) × List Unit =>
      x.1.2.elim (fun _ => (.inl (dF x.1.1 : ℤ) : Answer)) fun q =>
        q.elim (fun _ => (.inr ((rg x.1.1).map fun i : ℕ => (i : ℤ) + sh x.1.1) : Answer)) fun q =>
          q.elim (fun q => (.inl (capF (q.1, x.1.1, (q.2 - sh x.1.1).toNat) : ℤ) : Answer)) fun q =>
            q.elim (fun q => (.inl (val (x.2, (x.1.1, (q.1 - sh x.1.1).toNat), q.2)) : Answer)) fun q =>
              (.inl (bif q.1.2 then bot ((x.2, q.1.1), (0, (q.2.1 - sh x.1.1).toNat), q.2.2) else top ((x.2, q.1.1), (0, (q.2.1 - sh x.1.1).toNat), q.2.2)) : Answer) := by sorry
