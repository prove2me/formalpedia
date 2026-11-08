-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_wordLinearMapTranspose_tannerBoundary_basis_apply_of_not_incident
-- name    : QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_tannerBoundary_basis_apply_of_not_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:24:27.296667+00:00
-- url     : https://prove2.me/theorems/57ee09d0-4aa1-4eae-912e-e43661c92aa8
-- title:
--   LPSTanner: word Linear Map Transpose tanner Boundary basis apply of not incident
-- statement:
--   The LPSTanner construction uses the word Linear Map Transpose tanner Boundary basis apply of not incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L740-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L740-L758

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

theorem QEC.Coding.BalancedProduct.LPSTanner.wordLinearMapTranspose_tannerBoundary_basis_apply_of_not_incident
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) (j : Fin 200)
    (e : Edge401 q hq) (hg : g ∉ e.1) :
    wordLinearMapTranspose (tannerBoundary q hq40 hq)
      (canonicalBasisWord (g, j)) e = 0 := by sorry
