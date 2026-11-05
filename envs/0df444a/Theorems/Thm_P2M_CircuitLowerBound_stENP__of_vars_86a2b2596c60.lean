-- Prove2me | Theorems.Thm_P2M_CircuitLowerBound_stENP__of_vars_86a2b2596c60
-- name    : P2M_CircuitLowerBound_stENP__of_vars_86a2b2596c60
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:12.143006+00:00
-- url     : https://prove2.me/theorems/7277d293-5255-427b-a668-c0c455883a6b
-- title:
--   P2 M Circuit Lower Bound st ENP  of vars 86a2b2596c60: P2 M Circuit Lower Bound st ENP  of vars 86a2b2596c60
-- statement:
--   The language L0 is in E^NP, in the form with a machine that is started again after every answer;
--   with the bound on the variables as a hypothesis.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L83-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L83-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open Restart

theorem P2M_CircuitLowerBound_stENP__of_vars_86a2b2596c60 (h1 : StCertSched) (h2 : StCertTabF) (h3 : StFlip) (h4 : StVars) : StENP' := by sorry

alias «CircuitLowerBound».«stENP'_of_vars» := P2M_CircuitLowerBound_stENP__of_vars_86a2b2596c60
