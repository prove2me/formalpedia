-- Prove2me | Theorems.Thm_ThreeSatPrinted_SATCp_polyTimeSteps
-- name    : ThreeSatPrinted.SATCp_polyTimeSteps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:34:24.193193+00:00
-- url     : https://prove2.me/theorems/abc53765-4f68-42a4-82fb-dd15b26e5102
-- title:
--   Three Sat Printed: SATCp poly Time Steps
-- statement:
--   The steps of `SATCp ℓ τ` are polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L55-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L55-L55

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

theorem ThreeSatPrinted.SATCp_polyTimeSteps (ℓ τ : ℕ) : PolyTimeSteps (SATCp ℓ τ) := by sorry
