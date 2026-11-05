-- Prove2me | Theorems.Thm_SatK_sTM_eq_zero_of
-- name    : SatK.sTM_eq_zero_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:12.68649+00:00
-- url     : https://prove2.me/theorems/a9055d9e-8392-4998-9c55-2fca9f57fd84
-- title:
--   Sat K: s TM eq zero of
-- statement:
--   If k-SAT is in time O(2^{δn}) for every δ > 0, then s_k = 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/EndLemmas.lean#L19-L22
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/EndLemmas.lean#L19-L22

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_WidthK_Top_EndLemmas
set_option autoImplicit false
section
open SatK
open scoped NNReal ENNReal

theorem SatK.sTM_eq_zero_of {k : ℕ} (h : ∀ δ : ℝ≥0, 0 < δ → InTimeTM k δ) : sTM k = 0 := by sorry
