-- Prove2me | Theorems.Thm_PiecesCounted_computes_of_answer
-- name    : PiecesCounted.computes_of_answer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:21:07.741189+00:00
-- url     : https://prove2.me/theorems/3387b050-cda8-47b6-9acc-790f6193eb78
-- title:
--   Pieces Counted: computes of answer
-- statement:
--   A function of the question and a padding string that gives the right answer at 2^{kλ} units, k ≤
--   c, gives an algorithm within 2^{c'λ} operations, for every c' ≥ c with c' > k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Padded.lean#L126-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Padded.lean#L126-L150

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.computes_of_answer {D : Data} {ρ : ℝ} {c c' k : ℕ} (hD : D.Is ρ c) (hk : k ≤ c) (hc : c ≤ c') (hk' : k + 1 ≤ c') {f : (List Unit × Question) × List Unit → Answer}
    (hf : ∀ g a, D.oracle g = some a → f (g, List.replicate (2 ^ (k * g.1.length)) ()) = a) : Computes (padThen (fun g => 2 ^ (k * g.1.length)) f) D c' := by sorry
