-- Prove2me | Theorems.Thm_PaddedDescent_withBrute_polyT
-- name    : PaddedDescent.withBrute_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:16:34.14161+00:00
-- url     : https://prove2.me/theorems/5d42dcaf-4349-46f7-b69a-0205da6ef815
-- title:
--   Padded Descent: with Brute poly T
-- statement:
--   The algorithm with its two branches is polynomial-time if `A` is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L57-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L57-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_PaddedDescent_Reduce
set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing

theorem PaddedDescent.withBrute_polyT (s₀ : ℕ) {A : List Bool × List Unit → Bool} (hA : PolyT A) : PolyT (withBrute s₀ A) := by sorry
