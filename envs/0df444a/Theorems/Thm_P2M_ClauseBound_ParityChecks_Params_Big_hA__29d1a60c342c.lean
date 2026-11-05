-- Prove2me | Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
-- name    : P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:00.565768+00:00
-- url     : https://prove2.me/theorems/32635ae5-cd85-48e1-836e-b0a2dadd087b
-- title:
--   P2 M Clause Bound Parity Checks Params Big h A  29d1a60c342c: P2 M Clause Bound Parity Checks Params Big h A  29d1a60c342c
-- statement:
--   84·c·t + 84·t ≤ ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L190-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L190-L193

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

theorem P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c : 84 * (c * t) + 84 * t ≤ ℓ := by sorry

alias «ClauseBound».«ParityChecks».«Params».«Big».«hA'» := P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
