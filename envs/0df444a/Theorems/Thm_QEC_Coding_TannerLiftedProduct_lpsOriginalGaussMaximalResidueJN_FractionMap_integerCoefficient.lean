-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_FractionMap_integerCoefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_FractionMap_integerCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:27:03.917117+00:00
-- url     : https://prove2.me/theorems/381d11f1-61fd-4485-9d5c-20d0aad965d0
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue JN Fraction Map integer Coefficient
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue JN Fraction Map integer Coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L242-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L242-L254

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_FractionMap_integerCoefficient
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).comp
      ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by sorry
