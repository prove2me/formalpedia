-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_mem_primalSupportVertices_iff
-- name    : QEC.Coding.BalancedProduct.LPSTannerExpansion.mem_primalSupportVertices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:29:26.322684+00:00
-- url     : https://prove2.me/theorems/bd33da46-6a6d-42a9-8378-5c728ac6e1a0
-- title:
--   LPSTanner Expansion: mem primal Support Vertices iff
-- statement:
--   The LPSTanner Expansion construction uses the mem primal Support Vertices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L218-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean#L218-L226

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

theorem QEC.Coding.BalancedProduct.LPSTannerExpansion.mem_primalSupportVertices_iff
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    g ∈ primalSupportVertices q hq40 hq x ↔
      localView q hq40 hq g x ≠ 0 := by sorry
