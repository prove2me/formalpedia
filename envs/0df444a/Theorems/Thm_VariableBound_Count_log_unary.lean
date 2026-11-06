-- Prove2me | Theorems.Thm_VariableBound_Count_log_unary
-- name    : VariableBound.Count.log_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:49:54.306326+00:00
-- url     : https://prove2.me/theorems/6c9e013c-0f88-4ac0-88dd-46b0898c15be
-- title:
--   Count: log unary
-- statement:
--   ⌊log₂ n⌋ is given in unary if n is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Cert.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Cert.lean#L65-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net
variable {α : Type} [Enc α]

theorem VariableBound.Count.log_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => Nat.log 2 (n x) := by sorry
