-- Prove2me | Theorems.Thm_VariableBound_Search_stepD_cases
-- name    : VariableBound.Search.stepD_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:41:25.063482+00:00
-- url     : https://prove2.me/theorems/dffb0032-ed85-46e1-a36d-63c10da0c21e
-- title:
--   Search: step D cases
-- statement:
--   A step of `argminD` returns the new pair or the old state.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L52-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L52-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Search_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
omit [Enc α]

theorem VariableBound.Search.stepD_cases (key : List ℕ → ℤ) (best : Option (List ℕ × ℤ)) (l : List ℕ) : stepD key best l = some (l, key l) ∨ stepD key best l = best := by sorry
