-- Prove2me | Theorems.Thm_VariableBound_Paper_timeCor_eq
-- name    : VariableBound.Paper.timeCor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:03.843183+00:00
-- url     : https://prove2.me/theorems/f945c782-8c2e-4677-9e07-815f0960882c
-- title:
--   Paper: time Cor eq
-- statement:
--   min{2^{C·a}, 2^{C·b}} = 2^{C·min{a, b}}: the time of Corollary 11 is the time of Theorem 1. No
--   hypothesis on C, k, m, n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L225-L229
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L225-L229

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_VariableBound_Paper_Arith
set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms

theorem VariableBound.Paper.timeCor_eq (C k m n : ℕ) : timeCor C k m n = timeMin C k m n := by sorry
