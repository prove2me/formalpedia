-- Prove2me | Theorems.Thm_Variance_stHence
-- name    : Variance.stHence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:35:22.249487+00:00
-- url     : https://prove2.me/theorems/2e4827e1-1a3c-4730-bbd2-eab4bda58f69
-- title:
--   Variance: st Hence
-- statement:
--   **«Hence»**, for any numbers κ(p, q) in the place of the covariances: if κ vanishes for disjoint
--   pairs, κ(p, q) ≤ m for all pairs and m ≥ 0, then Σ_p Σ_q c_p·c_q·κ(p, q) ≤ Σ_p c_p·4P·m = 4PU·m, for
--   c symmetric with (i) of Definition 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L103-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L103-L128

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

theorem Variance.stHence : StHence := by sorry
