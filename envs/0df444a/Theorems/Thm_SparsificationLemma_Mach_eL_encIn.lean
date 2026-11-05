-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_eL_encIn
-- name    : SparsificationLemma.Mach.eL_encIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:27:17.888698+00:00
-- url     : https://prove2.me/theorems/489e8297-974e-4a4e-8ec4-fdc4ea0c62b4
-- title:
--   Mach: e L enc In
-- statement:
--   The exponent of the pad on the input 1^s 0 1^k 0 code(φ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L138-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L138-L141

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo

theorem SparsificationLemma.Mach.eL_encIn (s k n : ℕ) (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) :
    eL (encIn s k φ) = n / 2 ^ s + k + 3 * Nat.size (encIn s k φ).length + 9 := by sorry
