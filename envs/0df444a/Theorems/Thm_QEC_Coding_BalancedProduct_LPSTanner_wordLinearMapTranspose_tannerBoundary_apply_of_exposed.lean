-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_wordLinearMapTranspose_tannerBoundary_apply_of_exposed
-- name    : QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_tannerBoundary_apply_of_exposed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:37.123659+00:00
-- url     : https://prove2.me/theorems/8594484c-ab5b-45fa-95f6-108ab617e98d
-- title:
--   LPSTanner: word Linear Map Transpose tanner Boundary apply of exposed
-- statement:
--   If exactly one endpoint of an edge carries a nonzero check block, the
--   global transpose on that edge is that endpoint's local transpose entry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L718-L738
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L718-L738

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

theorem QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_tannerBoundary_apply_of_exposed
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1)
    (hother : ∀ w : Vertex401 q, w ∈ e.1 → w ≠ g →
      checkBlock q w y = 0) :
    wordLinearMapTranspose (tannerBoundary q hq40 hq) y e =
      wordLinearMapTranspose localParityCheck (checkBlock q g y)
        (edgeLocalCoordinate q hq40 hq e g hg) := by sorry
