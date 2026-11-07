-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_separable
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_separable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:26:01.042703+00:00
-- url     : https://prove2.me/theorems/12a59e0a-c325-4dae-a942-ca52f06bfd0c
-- title:
--   Tanner Lifted Product: lps Original Modular Polynomial Mod Fraction separable
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Modular Polynomial Mod Fraction separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L281-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCoprimeModularReduction.lean#L281-L313

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_separable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalModularPolynomialModFraction N hN p).Separable := by sorry
