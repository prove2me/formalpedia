-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:30:57.39779+00:00
-- url     : https://prove2.me/theorems/899237df-2452-4d53-b33b-e65f8e238df6
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic uniform cusp pole clearing
-- statement:
--   One actual natural power clears the poles at all finitely many original cusps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L261-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L261-L299

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    ∃ k : ℕ, ∀ c : CuspOrbits
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      AnalyticAt ℂ (fun q : ℂ => q^k *
        F ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by sorry
