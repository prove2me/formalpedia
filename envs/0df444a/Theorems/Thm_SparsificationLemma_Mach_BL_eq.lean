-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_BL_eq
-- name    : SparsificationLemma.Mach.BL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:02.861338+00:00
-- url     : https://prove2.me/theorems/a69dcf7e-42de-4208-afdb-10f103ca21a5
-- title:
--   Mach: BL eq
-- statement:
--   On 1^s 0 1^k 0 code(φ), for k ≥ 1, s ≥ `s0U k` and φ a k-CNF without an empty clause, and with
--   the pad of 2^(eL …) units, `BL` is the code of the list of outputs for τ = 2^(4s+17).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L191-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L191-L220

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Len
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo

theorem SparsificationLemma.Mach.BL_eq (k n s : ℕ) (φ : Sat3.CNF n) (hk : 1 ≤ k) (hs : s0U k ≤ s) (hφ : SatK.IsKCNF k φ) (hnil : [] ∉ φ) :
    BL (encIn s k φ, PaddedDescent.pad (eL (encIn s k φ))) = code (outTau k n (tauOf s) (Decode.toN φ)) := by sorry
