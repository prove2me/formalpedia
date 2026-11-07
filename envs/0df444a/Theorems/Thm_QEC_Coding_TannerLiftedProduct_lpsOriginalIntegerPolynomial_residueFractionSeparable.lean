-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_residueFractionSeparable
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_residueFractionSeparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:46.017842+00:00
-- url     : https://prove2.me/theorems/3ec42bce-345d-4d18-a4d9-435f3f100993
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial residue Fraction Separable
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Polynomial residue Fraction Separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L256-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L256-L271

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldCuspSeries_domain

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_residueFractionSeparable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ((lpsOriginalIntegerPolynomial N hN).map
      ((algebraMap (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp))
          (FractionRing (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp)))).comp
        (lpsOriginalResidueLevelCoefficientEval N hN p hp))).Separable := by sorry
