-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_layersF_eq
-- name    : PaddedDescent.F.Eval.layersF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:47.850318+00:00
-- url     : https://prove2.me/theorems/22e5cfd3-2441-4aea-a26c-6338f6e9aaf0
-- title:
--   Eval: layers F eq
-- statement:
--   The layers that the program chooses are those of the generic choice with the program's
--   evaluation function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L214-L219
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L214-L219

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

theorem PaddedDescent.F.Eval.layersF_eq {k n R m : ℕ} {pad : U} (hpad : layLen k n m R ≤ pad.length) (S : List Lvl × U) (p : U × U × U × U) (ψ : Fml)
    (hψ : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hm : ψ.length ≤ m) :
    layersF k pad S p R ψ = layersE (evalF k pad S p) p.2.1.length R ψ := by sorry
