-- Prove2me | Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big___ge_9297678cfbb5
-- name    : P2M_ClauseBound_ParityChecks_Params_Big___ge_9297678cfbb5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:47.77038+00:00
-- url     : https://prove2.me/theorems/0b0b55ed-6802-4d42-8a72-4f6280dcff65
-- title:
--   P2 M Clause Bound Parity Checks Params Big   ge 9297678cfbb5: P2 M Clause Bound Parity Checks Params Big   ge 9297678cfbb5
-- statement:
--   The P2 M Clause Bound Parity Checks Params Big   ge 9297678cfbb5 construction uses the P2 M Clause Bound Parity Checks Params Big   ge 9297678cfbb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L195-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L195-L196

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b

theorem P2M_ClauseBound_ParityChecks_Params_Big___ge_9297678cfbb5 : 84 ≤ ℓ := by sorry

alias «ClauseBound».«ParityChecks».«Params».«Big».«ℓ_ge» := P2M_ClauseBound_ParityChecks_Params_Big___ge_9297678cfbb5
