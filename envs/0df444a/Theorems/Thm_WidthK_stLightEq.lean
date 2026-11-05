-- Prove2me | Theorems.Thm_WidthK_stLightEq
-- name    : WidthK.stLightEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:34:47.003018+00:00
-- url     : https://prove2.me/theorems/70386993-177e-47bf-8984-a6662b7209ca
-- title:
--   Width K: st Light Eq
-- statement:
--   `SetAlg.light_eq` as an interface statement.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L131-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L131-L131

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

theorem WidthK.stLightEq : StLightEq := by sorry
