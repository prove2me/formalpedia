-- Prove2me | Theorems.Thm_UniformInK_FallBack_logb_le
-- name    : UniformInK.FallBack.logb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:41.159825+00:00
-- url     : https://prove2.me/theorems/06184c22-ea86-4d2e-a3f4-1bd411477b27
-- title:
--   Fall Back: logb le
-- statement:
--   log₂(n+4) ≤ ⌊log₂ n⌋ + 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/FallBack.lean#L25-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/FallBack.lean#L25-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_UniformInK_Top_FallBack
set_option autoImplicit false
section
section
open UniformInK UniformInK.FallBack
open ClauseBound.TopN.GenN

theorem UniformInK.FallBack.logb_le (n : ℕ) : Real.logb 2 ((n : ℝ) + 4) ≤ (Nat.log 2 n : ℝ) + 3 := by sorry
