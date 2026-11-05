-- Prove2me | Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d
-- name    : P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:26.896813+00:00
-- url     : https://prove2.me/theorems/24f340a6-d1ca-4547-832e-33247a2f4823
-- title:
--   P2 M Clause Bound Parity Checks Params two   le d18f4ddaa33d: P2 M Clause Bound Parity Checks Params two   le d18f4ddaa33d
-- statement:
--   2Δ ≤ 2^{⌈log₂(2Δ)⌉}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L165-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L165-L165

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

theorem P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d (Δ : ℕ) : 2 * Δ ≤ 2 ^ LD Δ := by sorry

alias «ClauseBound».«ParityChecks».«Params».«two_Δ_le» := P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d
