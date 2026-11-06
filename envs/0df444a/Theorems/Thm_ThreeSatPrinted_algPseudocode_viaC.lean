-- Prove2me | Theorems.Thm_ThreeSatPrinted_algPseudocode_viaC
-- name    : ThreeSatPrinted.algPseudocode_viaC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:33:18.111035+00:00
-- url     : https://prove2.me/theorems/47badfd5-4a1e-40a9-a797-e853cbd9c92e
-- title:
--   Three Sat Printed: alg Pseudocode via C
-- statement:
--   **Algorithm 1 decides 3-SAT within c·2^{δn} steps**, with the level chosen as in the header of
--   Algorithm 1: for every δ > 0 there are a parameter τ ≥ 24 and δ' = min(δ/(3M), 1), M = 2·(θ 0 + θ 1 +
--   θ 2), such that `SATCp ℓ τ` with «ℓ the first level with K_ℓ ≥ 72/δ' and
--   e_ℓ ≤ δ'/12» decides 3-SAT on n variables within c·2^{δn} steps. Different from the paper: δ' =
--   min(δ/(3M), 1) (the paper assumes δ ≤ 1 and has δ' = δ/(3M)); M is the bound per variable on the
--   clauses of a leaf of the tree walked by `satC τ`, not the M(δ/3) of Lemma 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L63-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/ThmEveryDelta.lean#L63-L69

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

theorem ThreeSatPrinted.algPseudocode_viaC {δ : ℝ} (hδ : 0 < δ) :
    ∃ (τ : ℕ) (δ' : ℝ) (hδ' : 0 < δ'), 24 ≤ τ ∧ δ' = min (δ / (3 * (leafCU τ 3 : ℝ))) 1 ∧ Paper.DecidesInSteps (SATCp (Level.firstLevel hδ') τ) δ := by sorry
