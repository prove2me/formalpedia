-- Prove2me | Theorems.Thm_WidthK_Refine_tryP_some
-- name    : WidthK.Refine.tryP_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:45.006747+00:00
-- url     : https://prove2.me/theorems/30963edc-987a-4646-968e-e510af0a0532
-- title:
--   Refine: try P some
-- statement:
--   An answer of `tryP` at the pair (j, h) is a heart of size h for the clauses of size j, without
--   repeated literals, with its petals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L241-L254
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L241-L254

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.tryP_some {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {jh : ℕ × ℕ} {HP : PCl × PFml} (hs : NF s) (hjh : jh ∈ pairsK k)
    (h : tryP θ k s jh = some HP) :
    HP.1.Nodup ∧ HP.1.toFinset.card = jh.2 ∧ Heart θ (toFin s) jh.1 HP.1.toFinset ∧
      HP.2 = (overP s jh.1 HP.1).map (minusP HP.1) := by sorry
