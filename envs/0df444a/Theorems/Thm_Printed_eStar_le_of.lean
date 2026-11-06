-- Prove2me | Theorems.Thm_Printed_eStar_le_of
-- name    : Printed.eStar_le_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:32:07.349287+00:00
-- url     : https://prove2.me/theorems/16000a36-244c-4f55-855f-a55cd2bf06e8
-- title:
--   Printed: e Star le of
-- statement:
--   «Let e > e*; then (K, e) is achievable for infinitely many K. Let e'' > ρe. For all large K we
--   have (ρ + 2/K)e + 2/K ≤ e'', so (9K¹⁶, e'') is achievable for infinitely many K, and therefore e* ≤
--   e''.» «Large» is K ≥ (2e + 2)/(e'' − ρe); 9K¹⁶ is written (3K⁸)².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelSentences.lean#L46-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelSentences.lean#L46-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelCost
import Definitions.Def_Eight_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Printed_LevelSentences
import Theorems.Thm_Eight_eStar_le_of

set_option autoImplicit false
section
section
open Printed
open Eight Paper QueryMachines

theorem Printed.eStar_le_of (hP3 : LevelProposition) {e e'' : ℝ} (he : eStar < e) (he'' : rho * e < e'') : eStar ≤ e'' := by sorry
