-- Prove2me | Theorems.Thm_WidthK_Prog_pickK_eq
-- name    : WidthK.Prog.pickK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:35:39.338063+00:00
-- url     : https://prove2.me/theorems/eb323383-46ec-4ae6-a138-158cfc9ea429
-- title:
--   Prog: pick K eq
-- statement:
--   `pickK` as a search along the list of the pairs (j, h) of a clause size j and a heart size h,
--   each with its threshold θ (j - h). This list does not depend on the input, so θ, an arbitrary
--   function, is never applied to a value computed from the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L53-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean#L53-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open WidthK WidthK.Prog
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]

theorem WidthK.Prog.pickK_eq (θ : ℕ → ℕ) (k : ℕ) (s : PFml) :
    pickK θ k s = (((pairsK k).map fun jh => (jh, θ (jh.1 - jh.2))).filterMap (tryT k s)).head? := by sorry
