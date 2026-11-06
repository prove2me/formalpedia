-- Prove2me | Theorems.Thm_PairsToBound_both_le_polyT
-- name    : PairsToBound.both_le_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:29.721423+00:00
-- url     : https://prove2.me/theorems/d54eeeff-fa7e-4206-85c7-4b2dee8606f5
-- title:
--   Pairs To Bound: both le poly T
-- statement:
--   Comparing two polynomial-time numbers with a third is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L140-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/FrontEnd.lean#L140-L141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_FrontEnd
set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
variable {α : Type} [Enc α]

theorem PairsToBound.both_le_polyT {a b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) : PolyT fun x => decide (a x ≤ c x) && decide (b x ≤ c x) := by sorry
