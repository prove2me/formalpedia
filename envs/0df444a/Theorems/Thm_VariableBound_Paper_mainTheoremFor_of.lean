-- Prove2me | Theorems.Thm_VariableBound_Paper_mainTheoremFor_of
-- name    : VariableBound.Paper.mainTheoremFor_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:55.617203+00:00
-- url     : https://prove2.me/theorems/4512b748-5572-4d1b-8506-60cb51aa5243
-- title:
--   Paper: main Theorem For of
-- statement:
--   From the bound with the minimum of `UniformInKStatement.lean` (for k ≥ 1, n ≥ 1, all variables
--   occurring) with the constant C to the bound of Theorem 1 with the constant 3C, for the same machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L60-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L60-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Forms
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)

theorem VariableBound.Paper.mainTheoremFor_of {M : TM2ComputableAux Bool Bool} {C : ℕ}
    (h : ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ → SatM.AllOccur φ →
      CountsWithin M k φ (SatM.boundBothK (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) C k n φ.length)) : MainTheoremFor M (3 * C) := by sorry
