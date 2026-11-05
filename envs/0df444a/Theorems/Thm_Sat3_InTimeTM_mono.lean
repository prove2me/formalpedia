-- Prove2me | Theorems.Thm_Sat3_InTimeTM_mono
-- name    : Sat3.InTimeTM.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:20:29.7924+00:00
-- url     : https://prove2.me/theorems/0f200519-41dc-49bb-8834-10c7089b8e7b
-- title:
--   In Time TM: mono
-- statement:
--   More time is allowed for a larger δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EndLemmas.lean#L29-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EndLemmas.lean#L29-L34

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

theorem Sat3.InTimeTM.mono {δ δ' : ℝ≥0} (h : InTimeTM δ) (hδ : δ ≤ δ') : InTimeTM δ' := by sorry
