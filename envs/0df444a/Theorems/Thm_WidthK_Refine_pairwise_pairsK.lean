-- Prove2me | Theorems.Thm_WidthK_Refine_pairwise_pairsK
-- name    : WidthK.Refine.pairwise_pairsK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:29.684512+00:00
-- url     : https://prove2.me/theorems/8103c9aa-0375-49a2-8c11-2a0e96cdb8cf
-- title:
--   Refine: pairwise pairs K
-- statement:
--   `pairsK k` lists its pairs in the order `Before`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L179-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L179-L189

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

theorem WidthK.Refine.pairwise_pairsK (k : ℕ) : (pairsK k).Pairwise Before := by sorry
