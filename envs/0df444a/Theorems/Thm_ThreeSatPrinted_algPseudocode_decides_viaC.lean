-- Prove2me | Theorems.Thm_ThreeSatPrinted_algPseudocode_decides_viaC
-- name    : ThreeSatPrinted.algPseudocode_decides_viaC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:34:07.202202+00:00
-- url     : https://prove2.me/theorems/4b1cde30-46a5-4e67-afea-fa5503e17fe6
-- title:
--   Three Sat Printed: alg Pseudocode decides via C
-- statement:
--   **Theorem 2 in its decision form for step machines, with the machine named.** For every δ > 0
--   there are a level ℓ and a parameter τ ≥ 24 such that `SATCp ℓ τ` has polynomial-time steps and
--   decides 3-SAT on n variables within c·2^{δn} steps. (`algPseudocode_viaC` says which ℓ and τ.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L74-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L74-L76

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

theorem ThreeSatPrinted.algPseudocode_decides_viaC {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ : ℕ, 24 ≤ τ ∧ PolyTimeSteps (SATCp ℓ τ) ∧ Paper.DecidesInSteps (SATCp ℓ τ) δ := by sorry
