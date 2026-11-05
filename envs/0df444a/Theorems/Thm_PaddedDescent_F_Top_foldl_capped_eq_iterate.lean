-- Prove2me | Theorems.Thm_PaddedDescent_F_Top_foldl_capped_eq_iterate
-- name    : PaddedDescent.F.Top.foldl_capped_eq_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:14:33.719186+00:00
-- url     : https://prove2.me/theorems/984f1873-bf9d-48db-b504-5b58c45209f4
-- title:
--   Top: foldl capped eq iterate
-- statement:
--   A fold that applies f and then a cut-off cp in every round equals the iterate of f, if the
--   cut-off leaves all iterates alone.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L43-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L43-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem PaddedDescent.F.Top.foldl_capped_eq_iterate {γ ι : Type} (cp f : γ → γ) (P : γ → Prop) (hcp : ∀ x, P x → cp x = x) (l : List ι) (a : γ)
    (h : ∀ i ≤ l.length, P (f^[i] a)) : l.foldl (fun st _ => cp (f st)) (cp a) = f^[l.length] a := by sorry
