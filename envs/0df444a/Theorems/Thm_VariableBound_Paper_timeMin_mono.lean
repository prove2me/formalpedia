-- Prove2me | Theorems.Thm_VariableBound_Paper_timeMin_mono
-- name    : VariableBound.Paper.timeMin_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:29.941477+00:00
-- url     : https://prove2.me/theorems/50dd7821-2f8a-4dc2-a7b6-6c0c9ed72550
-- title:
--   Paper: time Min mono
-- statement:
--   The printed bound of Theorem 1 grows with the constant, for k ≥ 1, m ≥ 2 and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L218-L221
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Arith.lean#L218-L221

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

theorem VariableBound.Paper.timeMin_mono {C C' : ℕ} (h : C ≤ C') {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) : timeMin C k m n ≤ timeMin C' k m n := by sorry
