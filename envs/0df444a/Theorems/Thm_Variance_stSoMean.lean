-- Prove2me | Theorems.Thm_Variance_stSoMean
-- name    : Variance.stSoMean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:34:31.712352+00:00
-- url     : https://prove2.me/theorems/bf15c7eb-15f2-45c4-9d9d-e20bce8fe82b
-- title:
--   Variance: st So Mean
-- statement:
--   «so 𝔼Y_{γ,γ'} = U/K²», from the two statements before it: Y_{γ,γ'} is the sum of c_{a,b} over
--   the ordered pairs (a, b) that contribute (`StYIsSum`), and «Each ordered pair (a,b) contributes with
--   probability 1/K²» (`StPairProb`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L32-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L32-L41

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

theorem Variance.stSoMean : StSoMean := by sorry
