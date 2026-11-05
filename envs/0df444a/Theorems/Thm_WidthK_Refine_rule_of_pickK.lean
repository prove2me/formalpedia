-- Prove2me | Theorems.Thm_WidthK_Refine_rule_of_pickK
-- name    : WidthK.Refine.rule_of_pickK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:59.928661+00:00
-- url     : https://prove2.me/theorems/8f56166b-a478-4656-b036-2d0e8a9b94a0
-- title:
--   Refine: rule of pick K
-- statement:
--   An answer of `pickK` satisfies `Rule`: smallest clause size that has a heart, then a heart of
--   the largest size.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L291-L301
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L291-L301

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

theorem WidthK.Refine.rule_of_pickK {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {HP : PCl × PFml} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (h : pickK θ k s = some HP) :
    ∃ j, HP.1.Nodup ∧ Rule θ k (toFin s) j HP.1.toFinset ∧ HP.2 = (overP s j HP.1).map (minusP HP.1) := by sorry
