-- Prove2me | Theorems.Thm_VariableBound_Arith_of_BkD
-- name    : VariableBound.Arith.of_BkD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:50.337997+00:00
-- url     : https://prove2.me/theorems/87953466-1c16-419b-ac82-127608de5b9a
-- title:
--   Arith: of Bk D
-- statement:
--   From B·k² ≤ ℓ with B = `BkD C C₀`: the condition 2·(102·C₀·c)² ≤ ℓ of `UniformInK.StSixU` for c =
--   a·k, a = `aU C C₀`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L51-L53

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

theorem VariableBound.Arith.of_BkD {C C₀ k ℓ : ℕ} (h : BkD C C₀ * k ^ 2 ≤ ℓ) : 2 * (102 * C₀ * (aU C C₀ * k)) ^ 2 ≤ ℓ := by sorry
