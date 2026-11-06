-- Prove2me | Theorems.Thm_PairsToBound_triesAllWithin_of_computes
-- name    : PairsToBound.triesAllWithin_of_computes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:11:46.710217+00:00
-- url     : https://prove2.me/theorems/a997b954-442e-41b1-9ed4-b89db2f064ef
-- title:
--   Pairs To Bound: tries All Within of computes
-- statement:
--   «… the algorithm tries all assignments; … this takes time 2^n·n^{O(k)}, reading the input
--   included.» Every machine that computes exhaustive counting with a padding string of 2ⁿ units, with
--   the constant q, tries all assignments within 2^{c·n}·n^{c·k} steps for c = 8q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L151-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L151-L157

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)

theorem PairsToBound.triesAllWithin_of_computes {Mb : TM2ComputableAux Bool Bool} {qb : ℕ} (h : Computes Mb exhaust (fun x => (fmlOf x).1.length) qb) : TriesAllWithin Mb (8 * qb) := by sorry
