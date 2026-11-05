-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_foldl_cap_eq
-- name    : PaddedDescent.F.Eval.foldl_cap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:03.707206+00:00
-- url     : https://prove2.me/theorems/b5da95ac-00d3-4043-bab9-4a4453aaf083
-- title:
--   Eval: foldl cap eq
-- statement:
--   No cut-off by the pad is active in the loop that places the clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L200-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L200-L210

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)

theorem PaddedDescent.F.Eval.foldl_cap_eq {k n R m : ℕ} {pad : U} (hpad : layLen k n m R ≤ pad.length) (ev : List Fml → ℤ) (w : ℕ) (ψ : Fml) :
    ∀ (Ls : List Fml) (c : ℕ), Form k n R c Ls → (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → c + ψ.length ≤ m →
      ψ.foldl (fun Ls C => cap pad [] (placeE ev w Ls C)) Ls = ψ.foldl (placeE ev w) Ls := by sorry
