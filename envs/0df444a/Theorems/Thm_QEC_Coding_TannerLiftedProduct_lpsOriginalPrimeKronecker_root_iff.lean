-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeKronecker_root_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeKronecker_root_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:56:28.288082+00:00
-- url     : https://prove2.me/theorems/da672d35-7647-407a-a984-b80579564ff1
-- title:
--   Tanner Lifted Product: lps Original Prime Kronecker root iff
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Kronecker root iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L114-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L114-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeKronecker_root_iff
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] (j y : A) :
    ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))).eval₂
      (Polynomial.eval₂RingHom (algebraMap (ZMod p) A) j) y = 0 ↔
      y=j^p ∨ y^p=j := by sorry
