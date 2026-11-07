-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetCuspResidueData_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspResidueData_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:17:33.812268+00:00
-- url     : https://prove2.me/theorems/489f6fcb-0927-4fd0-a163-e17d64b127ca
-- title:
--   Tanner Lifted Product: lps Original Coset Cusp Residue Data injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Cusp Residue Data injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L393-L412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L393-L412

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspResidueData_injective
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalCosetCuspResidueData N hN p hp) := by sorry
