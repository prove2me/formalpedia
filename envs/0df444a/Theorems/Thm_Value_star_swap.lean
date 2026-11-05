-- Prove2me | Theorems.Thm_Value_star_swap
-- name    : Value.star_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:16:07.386024+00:00
-- url     : https://prove2.me/theorems/8cba2716-9e81-4e19-b40a-5384124c8c47
-- title:
--   Value: star swap
-- statement:
--   The string of Λ on the edge {w, w'} is the same seen from w and from w'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L85-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L85-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Words
set_option autoImplicit false
section
section
open Value
open Groundwork Finset

theorem Value.star_swap {K : ℕ} (Λ : Fin K × Fin K → List Bool) (w w' : Fin K) : star Λ w w' = star Λ w' w := by sorry
