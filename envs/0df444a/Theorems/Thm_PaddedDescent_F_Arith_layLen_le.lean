-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_layLen_le
-- name    : PaddedDescent.F.Arith.layLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:51.169452+00:00
-- url     : https://prove2.me/theorems/79bebb7f-a63e-4d75-be2b-e07078deec25
-- title:
--   Arith: lay Len le
-- statement:
--   The field `lay` of `MarkFits`: the word of the layers fits under the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L72-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L72-L94

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

theorem PaddedDescent.F.Arith.layLen_le {k Δ n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) (hk : k ≤ sOf n)
    (hΔ : Δ ≤ 2 ^ betaOf (sOf n)) : layLen k n (Δ * n) (layersOf (sOf n)) ≤ F := by sorry
