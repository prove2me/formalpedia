-- Prove2me | Theorems.Thm_WidthK_Refine_refines
-- name    : WidthK.Refine.refines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:14.866453+00:00
-- url     : https://prove2.me/theorems/f2cde050-139c-4084-8e9e-70ec723b7aae
-- title:
--   Refine: refines
-- statement:
--   If the thresholds θ 1, θ 2, … are at least 1, then `pickK θ k` follows the rule on finite sets,
--   its petals are in normal form, and
--   `rootP` gives the inclusion-minimal clauses in normal form.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L324-L334
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L324-L334

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.refines {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (k : ℕ) : Refines θ k := by sorry
