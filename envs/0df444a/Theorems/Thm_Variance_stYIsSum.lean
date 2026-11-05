-- Prove2me | Theorems.Thm_Variance_stYIsSum
-- name    : Variance.stYIsSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:23:04.091635+00:00
-- url     : https://prove2.me/theorems/ae145ce0-816d-416c-8c28-8f5faf9625e2
-- title:
--   Variance: st YIs Sum
-- statement:
--   Y_{γ,γ'} is the sum of c_{a,b} over the ordered pairs that contribute.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L44-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L44-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Cov
set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks

theorem Variance.stYIsSum : StYIsSum := by sorry
