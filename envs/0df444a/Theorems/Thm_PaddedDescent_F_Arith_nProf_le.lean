-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_nProf_le
-- name    : PaddedDescent.F.Arith.nProf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:31.608612+00:00
-- url     : https://prove2.me/theorems/0f82d30e-7fe9-4dfb-99ae-f291e7904435
-- title:
--   Arith: n Prof le
-- statement:
--   The field `prof` of `MarkFits`: the pad has a unit for every number that is tried as a profile.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L57-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L57-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithMark
set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent

theorem PaddedDescent.F.Arith.nProf_le {Δ n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) (hΔ : Δ ≤ 2 ^ betaOf (sOf n)) :
    Mark.nProf (3 * Kseq (depthOf (sOf n)) ^ 8) (Δ * n) (layersOf (sOf n) + 2) ≤ F := by sorry
