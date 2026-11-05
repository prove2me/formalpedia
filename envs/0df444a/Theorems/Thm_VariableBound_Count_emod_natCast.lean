-- Prove2me | Theorems.Thm_VariableBound_Count_emod_natCast
-- name    : VariableBound.Count.emod_natCast
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:50:07.635089+00:00
-- url     : https://prove2.me/theorems/3cdf3c9a-1873-41ab-b3d6-28cd8b601938
-- title:
--   Count: emod nat Cast
-- statement:
--   The remainder of an integer modulo a natural number, by cases on the sign.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Cert.lean#L34-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Cert.lean#L34-L50

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

theorem VariableBound.Count.emod_natCast (a : ℤ) (b : ℕ) :
    a % (b : ℤ) = if 0 ≤ a then ((a.toNat % b : ℕ) : ℤ) else if b = 0 then a else ((b - 1 - (a.natAbs - 1) % b : ℕ) : ℤ) := by sorry
