-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_wordPairing_canonicalBasisWord_right
-- name    : QEC.Coding.BalancedProduct.LPSTanner.wordPairing_canonicalBasisWord_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:23:28.306262+00:00
-- url     : https://prove2.me/theorems/324e3dbb-f989-4395-8a6b-9ce95de78f1a
-- title:
--   LPSTanner: word Pairing canonical Basis Word right
-- statement:
--   The LPSTanner construction uses the word Pairing canonical Basis Word right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L213-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L213-L223

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

theorem QEC.Coding.BalancedProduct.LPSTanner.wordPairing_canonicalBasisWord_right
    {ι : Type*} [Fintype ι]
    (z : Word (ZMod 2) ι) (i : ι) :
    wordPairing z (canonicalBasisWord i) = z i := by sorry
