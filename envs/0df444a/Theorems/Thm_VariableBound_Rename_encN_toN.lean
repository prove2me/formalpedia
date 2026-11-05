-- Prove2me | Theorems.Thm_VariableBound_Rename_encN_toN
-- name    : VariableBound.Rename.encN_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:12:51.019661+00:00
-- url     : https://prove2.me/theorems/52c60b0f-e4b3-496a-9f3e-340fde71391f
-- title:
--   Rename: enc N to N
-- statement:
--   `encN` on k and n in unary and a formula over x₀ … x_(n−1), with natural numbers as variables,
--   is `SatM.enc`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Code.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Code.lean#L30-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Paper_Rename_Code
set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)

theorem VariableBound.Rename.encN_toN (k : ℕ) {n : ℕ} (φ : CNF n) : encN (List.replicate k ()) (List.replicate n (), toN φ) = SatM.enc k φ := by sorry
