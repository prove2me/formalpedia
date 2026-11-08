-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRight_density
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRight_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:04:40.357068+00:00
-- url     : https://prove2.me/theorems/ac815bf7-bde2-4ae5-a23b-4a38af149bca
-- title:
--   Tanner Lifted Product: lps Hecke Right density
-- statement:
--   The actual second factor identity transfers the original right Hecke density to the inverse cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L100-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L100-L123

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRight_density (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) (τ : ℍ) :
    petersson 2 f (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
        ((lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • τ) := by sorry
