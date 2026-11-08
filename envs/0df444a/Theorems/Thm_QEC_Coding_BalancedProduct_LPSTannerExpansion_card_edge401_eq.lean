-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_edge401_eq
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.card_edge401_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:23.864078+00:00
-- url     : https://prove2.me/theorems/8cfc7393-ba01-460e-abae-4314700cb657
-- title:
--   LPSTanner Expansion: card edge401 eq
-- statement:
--   Correct edge/vertex handshake normalization for the 402-regular LPS
--   graph: `|X₁| = 201 |X₀|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L187-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L187-L208

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTannerExpansion
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open LPSTanner LPSGraph GVPlus

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.card_edge401_eq
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (Edge401 q hq) =
      201 * Fintype.card (Vertex401 q) := by sorry
