-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeTwoCover_integrals
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeTwoCover_integrals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:02:13.492679+00:00
-- url     : https://prove2.me/theorems/e6b102a2-4000-49e4-866a-31f1c9b2f689
-- title:
--   Tanner Lifted Product: lps Hecke Two Cover integrals
-- statement:
--   The two actual covers give equal invariant mixed inverse-Petersson integrals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L169-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L169-L179

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeTwoCover_integrals (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    (∫τ in lpsHeckeUpperGL ℝ p none •
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s),
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ) =
      ∫τ in (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s),
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by sorry
