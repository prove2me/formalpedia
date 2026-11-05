-- Prove2me | Theorems.Thm_WidthK_stSatIff
-- name    : WidthK.stSatIff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:38:28.710206+00:00
-- url     : https://prove2.me/theorems/e2c2a14c-23ce-49f2-8730-ec1890441006
-- title:
--   Width K: st Sat Iff
-- statement:
--   `SetAlg.sat_iff` as an interface statement.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L137-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L137-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
set_option autoImplicit false
section
section
open WidthK

theorem WidthK.stSatIff : StSatIff := by sorry
