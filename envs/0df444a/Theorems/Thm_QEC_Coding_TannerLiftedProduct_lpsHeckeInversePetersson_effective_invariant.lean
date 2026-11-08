-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeInversePetersson_effective_invariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeInversePetersson_effective_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:02:21.219844+00:00
-- url     : https://prove2.me/theorems/6e8aa415-ae47-446d-86f5-90d521c40d63
-- title:
--   Tanner Lifted Product: lps Hecke Inverse Petersson effective invariant
-- statement:
--   The genuine mixed inverse-Petersson density is invariant under the effective intersection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L157-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L157-L166

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeInversePetersson_effective_invariant (N p : ℕ) [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveHeckeConjugateIntersection N p) (τ : ℍ) :
    petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) (h • τ) =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by sorry
