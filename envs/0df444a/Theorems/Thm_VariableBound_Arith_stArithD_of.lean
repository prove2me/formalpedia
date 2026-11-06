-- Prove2me | Theorems.Thm_VariableBound_Arith_stArithD_of
-- name    : VariableBound.Arith.stArithD_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:53.555209+00:00
-- url     : https://prove2.me/theorems/f9f6a6bd-278a-4c0b-bdad-953b84ea3f47
-- title:
--   Arith: st Arith D of
-- statement:
--   Steps 4 and 5, the exponent: with A = `AexpD C₀`, B = `BkD C C₀`, for k ≥ 1 and n ≥ K^17 (K the
--   number of nodes of the first level), l the level picked for n and s = s(l), the exponent of the
--   plan, or n if there is none,
--   is at most A·k²·n·e_l·(s+1), or ⌊log₂ n⌋ < B·k²; for a polynomial-time solver with a sequence of
--   levels and 2^(−s(l)) ≤ e_l, 2^(s(l)) ≤ (2/e_l)^C; from the interface statements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L128-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L128-L158

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_UniformInK_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithTop
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith

theorem VariableBound.Arith.stArithD_of (hN : StNeedD) (hP : StPlanLeD) (hPN : StPlanNeedD) (hM : StMasterU) (hDL : StDLogU) (h6 : StSixU) (hB : StBetaU) : StArithD := by sorry
