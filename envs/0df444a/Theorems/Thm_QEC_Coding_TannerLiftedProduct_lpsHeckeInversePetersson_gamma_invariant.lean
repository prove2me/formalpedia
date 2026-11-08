-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeInversePetersson_gamma_invariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeInversePetersson_gamma_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:02:16.841764+00:00
-- url     : https://prove2.me/theorems/ea87acd0-9dbb-4dd5-89da-7e7610ab9c7e
-- title:
--   Tanner Lifted Product: lps Hecke Inverse Petersson gamma invariant
-- statement:
--   Actual cusp slash invariance proves mixed inverse-Petersson invariance under the original intersection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L132-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L132-L154

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeInversePetersson_gamma_invariant (N p : ℕ) [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (δ : SL(2,ℤ)) (hδ : δ ∈ lpsHeckeConjugateIntersection N p) (τ : ℍ) :
    petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) (δ • τ) =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by sorry
