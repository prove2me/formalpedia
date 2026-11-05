-- Prove2me | Theorems.Thm_ThreeSatPrinted_satC_polyTimeSteps
-- name    : ThreeSatPrinted.satC_polyTimeSteps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:34:30.792695+00:00
-- url     : https://prove2.me/theorems/35198675-9dc7-4a98-b0e6-02ca2be60fea
-- title:
--   Three Sat Printed: sat C poly Time Steps
-- statement:
--   The steps of `satC τ Mc` are polynomial time if those of `Mc` are, for every τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L50-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatPrinted_Defs
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_Eight_Level_SecPseudocode
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_ThreeSatOnTree_ThmEveryDelta
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic.Positivity
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
set_option autoImplicit false
section
section
open ThreeSatPrinted
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight ThreeSatOnTree

theorem ThreeSatPrinted.satC_polyTimeSteps (τ : ℕ) {Mc : StepMachine Formula ℤ} (hMc : PolyTimeSteps Mc) : PolyTimeSteps (satC τ Mc) := by sorry
