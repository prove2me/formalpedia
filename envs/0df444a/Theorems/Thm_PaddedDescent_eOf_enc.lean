-- Prove2me | Theorems.Thm_PaddedDescent_eOf_enc
-- name    : PaddedDescent.eOf_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:03.880453+00:00
-- url     : https://prove2.me/theorems/ed730187-f877-4807-891c-deceed0e7762
-- title:
--   Padded Descent: e Of enc
-- statement:
--   On the code of an instance on n variables, `eOf` is `padLog` of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean#L44-L45

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

theorem PaddedDescent.eOf_enc (C₀ : ℕ) {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : eOf C₀ (enc φ) = padLog C₀ n := by sorry
