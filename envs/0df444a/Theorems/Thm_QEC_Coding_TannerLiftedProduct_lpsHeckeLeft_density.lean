-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeLeft_density
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeLeft_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:03:41.30322+00:00
-- url     : https://prove2.me/theorems/cf284790-b0e0-4129-8025-16d4d6c5f15a
-- title:
--   Tanner Lifted Product: lps Hecke Left density
-- statement:
--   The genuine first factor identity transfers the original left Hecke density to the A-image cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L72-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeAdjointDensities.lean#L72-L97

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeLeft_density (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) (τ : ℍ) :
    petersson 2 (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) g τ =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
        (lpsHeckeUpperGL ℝ p none •
          ((lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • τ)) := by sorry
