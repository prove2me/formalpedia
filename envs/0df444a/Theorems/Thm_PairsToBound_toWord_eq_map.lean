-- Prove2me | Theorems.Thm_PairsToBound_toWord_eq_map
-- name    : PairsToBound.toWord_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:41.982222+00:00
-- url     : https://prove2.me/theorems/c050fb8a-23c7-4f2b-8581-dcf7d75618e3
-- title:
--   Pairs To Bound: to Word eq map
-- statement:
--   The word of ℓ bits of y, lowest bit first, lists the binary digits number 0, …, ℓ − 1 of y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L61-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L61-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)

theorem PairsToBound.toWord_eq_map (l y : ℕ) : toWord l y = (List.range l).map y.testBit := by sorry
