-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_stU
-- name    : VariableBound.Net.SizeU.stU
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:22.555852+00:00
-- url     : https://prove2.me/theorems/e84c866c-8335-49fe-a453-6b6aa325d07d
-- title:
--   Size U: st U
-- statement:
--   Step 3, «The total», display (68) before display (61) is used: in the setting of Step 3 for m >
--   n̄, with g ≥ 1 nodes, the network of an admissible profile has U ≤ 6(k − 1)(n + log(2Δ)) +
--   2kM·log(96Δ·log(2Δ)) + 2g². Needs the
--   inequalities of «Setting and parameters» (the hypothesis `ParamIneq`, proved as
--   `VariableBound.paramIneq`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L231-L257
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L231-L257

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}

theorem VariableBound.Net.SizeU.stU (hp : ParamIneq) : StU := by sorry
