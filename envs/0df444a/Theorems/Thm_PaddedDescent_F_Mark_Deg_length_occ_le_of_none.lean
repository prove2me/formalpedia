-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_length_occ_le_of_none
-- name    : PaddedDescent.F.Mark.Deg.length_occ_le_of_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:01:57.623691+00:00
-- url     : https://prove2.me/theorems/bf628e67-443c-4dc3-9e07-2a1a21fa5721
-- title:
--   Deg: length occ le of none
-- statement:
--   Where `stepK` has no answer, every variable occurs in at most 2·(θ 0 + … + θ (k − 1)) clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L98-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L98-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)

theorem PaddedDescent.F.Mark.Deg.length_occ_le_of_none {θ : ℕ → ℕ} {k : ℕ} (hθ : ∀ i, 1 ≤ θ i) {x : PFml} (hx : NF x)
    (hcl : ∀ C ∈ x, C ≠ [] ∧ C.length ≤ k) (hst : stepK θ k x = none) (v : ℕ) : (occ x v).length ≤ 2 * ∑ i ∈ range k, θ i := by sorry
