-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:30:20.144509+00:00
-- url     : https://prove2.me/theorems/d1f4e17e-fa94-415a-b63f-dfdca06b2722
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic exists interior pole polynomial
-- statement:
--   A monic finite product of actual j-zero factors clears every actual interior pole.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L101-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L101-L182

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_interior_pole_polynomial
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∃ P : Polynomial ℂ, P.Monic ∧
      ∀ y : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      AnalyticAt ℂ (fun z => P.eval (lpsOriginalFilledJ N
        ((lpsOriginalFilledInteriorChart N hN y).symm z)) *
        F ((lpsOriginalFilledInteriorChart N hN y).symm z))
        (lpsOriginalFilledInteriorChart N hN y (Sum.inl y)) := by sorry
