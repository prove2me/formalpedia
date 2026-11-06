-- Prove2me | Theorems.Thm_Variance_stVarIsSumOfCov
-- name    : Variance.stVarIsSumOfCov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:34:33.866198+00:00
-- url     : https://prove2.me/theorems/fdb579cf-93ec-4d83-98d7-7bc78f216883
-- title:
--   Variance: st Var Is Sum Of Cov
-- statement:
--   The variance of Y is the sum of c_p·c_q·Cov(p, q) over all pairs of ordered pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L47-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L47-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Cov
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Var
set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks

theorem Variance.stVarIsSumOfCov : StVarIsSumOfCov := by sorry
