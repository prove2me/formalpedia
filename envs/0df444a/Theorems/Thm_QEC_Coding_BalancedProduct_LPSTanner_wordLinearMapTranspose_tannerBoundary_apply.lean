-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_wordLinearMapTranspose_tannerBoundary_apply
-- name    : QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_tannerBoundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:47.171168+00:00
-- url     : https://prove2.me/theorems/a5efa74d-076e-4849-87e9-caa59a1889e0
-- title:
--   LPSTanner: word Linear Map Transpose tanner Boundary apply
-- statement:
--   The LPSTanner construction uses the word Linear Map Transpose tanner Boundary apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L675-L714
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L675-L714

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype
set_option maxRecDepth 5000

theorem QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_tannerBoundary_apply
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (e : Edge401 q hq) :
    wordLinearMapTranspose (tannerBoundary q hq40 hq) y e =
      ∑ g : Vertex401 q,
        if hg : g ∈ e.1 then
          wordLinearMapTranspose localParityCheck (checkBlock q g y)
            (edgeLocalCoordinate q hq40 hq e g hg)
        else 0 := by sorry
