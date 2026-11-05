-- Prove2me | Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big___le_dae0589ea56c
-- name    : P2M_ClauseBound_ParityChecks_Params_Big___le_dae0589ea56c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:59.146327+00:00
-- url     : https://prove2.me/theorems/080b4cde-d362-4745-8450-2d312d05c925
-- title:
--   P2 M Clause Bound Parity Checks Params Big   le dae0589ea56c: P2 M Clause Bound Parity Checks Params Big   le dae0589ea56c
-- statement:
--   Δ ≤ 2^{c·t}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L215-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L215-L218

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

theorem P2M_ClauseBound_ParityChecks_Params_Big___le_dae0589ea56c : Δ ≤ 2 ^ (c * t) := by sorry

alias «ClauseBound».«ParityChecks».«Params».«Big».«Δ_le» := P2M_ClauseBound_ParityChecks_Params_Big___le_dae0589ea56c
