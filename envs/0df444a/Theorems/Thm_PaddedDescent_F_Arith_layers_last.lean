-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_layers_last
-- name    : PaddedDescent.F.Arith.layers_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:39.012213+00:00
-- url     : https://prove2.me/theorems/2e164659-a4c0-4668-b416-e1483a0ef070
-- title:
--   Arith: layers last
-- statement:
--   Field last of MarkFits: after `layersOf s` divisions, each of which keeps at most two thirds of
--   the clauses, fewer than n + 2 clauses are left.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L397-L417
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L397-L417

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.layers_last {Δ s n : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (hn : 6 ≤ n) :
    2 ^ layersOf s * (Δ * n) + 5 * 3 ^ layersOf s ≤ 3 ^ layersOf s * (n + 2) := by sorry
