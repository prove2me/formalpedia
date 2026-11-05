-- Prove2me | Theorems.Thm_VariableBound_Paper_countsWithin_mono
-- name    : VariableBound.Paper.countsWithin_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:26:29.660283+00:00
-- url     : https://prove2.me/theorems/f5e4858b-cebf-4eca-ba10-be4e16f3b7f0
-- title:
--   Paper: counts Within mono
-- statement:
--   A machine that counts within t steps counts within t' ≥ t steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L40-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Forms
set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)

theorem VariableBound.Paper.countsWithin_mono {M : TM2ComputableAux Bool Bool} {k n : ℕ} {φ : CNF n} {t t' : ℕ} (h : CountsWithin M k φ t) (ht : t ≤ t') : CountsWithin M k φ t' := by sorry
