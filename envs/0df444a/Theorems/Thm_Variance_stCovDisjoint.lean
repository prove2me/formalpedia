-- Prove2me | Theorems.Thm_Variance_stCovDisjoint
-- name    : Variance.stCovDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:33:26.988362+00:00
-- url     : https://prove2.me/theorems/9fe08214-eaaf-4bd5-830c-0d7e30667d23
-- title:
--   Variance: st Cov Disjoint
-- statement:
--   «The indicators of two ordered pairs have covariance 0 if the pairs are disjoint»: both
--   contribute with probability 1/K⁴ = (1/K²)·(1/K²).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L63-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L63-L72

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

theorem Variance.stCovDisjoint : StCovDisjoint := by sorry
