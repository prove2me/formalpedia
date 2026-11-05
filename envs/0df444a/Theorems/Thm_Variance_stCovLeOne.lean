-- Prove2me | Theorems.Thm_Variance_stCovLeOne
-- name    : Variance.stCovLeOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:34:47.53286+00:00
-- url     : https://prove2.me/theorems/75a407ed-1322-4c3d-85ce-d986237e2e95
-- title:
--   Variance: st Cov Le One
-- statement:
--   «and at most 1 otherwise»: an event has probability at most 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L75-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L75-L84

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

theorem Variance.stCovLeOne : StCovLeOne := by sorry
