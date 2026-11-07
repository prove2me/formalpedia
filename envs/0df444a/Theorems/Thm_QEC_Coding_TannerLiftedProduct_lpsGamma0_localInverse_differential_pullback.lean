-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_localInverse_differential_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0_localInverse_differential_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:45:16.151672+00:00
-- url     : https://prove2.me/theorems/4f681a19-bc79-4274-9094-eb38f1914705
-- title:
--   Tanner Lifted Product: lps Gamma0 local Inverse differential pullback
-- statement:
--   The true original quotient local inverse preserves the weight-two differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L194-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L194-L235

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0_localInverse_differential_pullback (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (σ τ : ℍ)
    (hs : Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ∈
      ((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ).source) :
    let e := (lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ
    let proj := Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    f (e (proj τ)) * deriv (fun z : ℂ => (e (proj (UpperHalfPlane.ofComplex z)) : ℂ)) τ =
      f τ := by sorry
