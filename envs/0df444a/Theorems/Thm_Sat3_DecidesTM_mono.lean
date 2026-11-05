-- Prove2me | Theorems.Thm_Sat3_DecidesTM_mono
-- name    : Sat3.DecidesTM.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:20:23.449753+00:00
-- url     : https://prove2.me/theorems/fd0536cc-5fed-4041-a7f5-8da5128d78b1
-- title:
--   Decides TM: mono
-- statement:
--   A machine that decides within t decides within any larger bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EndLemmas.lean#L22-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EndLemmas.lean#L22-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ToTuring_EndLemmas
set_option autoImplicit false
section
open Sat3
open Turing
open scoped NNReal ENNReal

theorem Sat3.DecidesTM.mono {M : TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (h : DecidesTM M t)
    (ht : ∀ n, t n ≤ t' n) : DecidesTM M t' := by sorry
