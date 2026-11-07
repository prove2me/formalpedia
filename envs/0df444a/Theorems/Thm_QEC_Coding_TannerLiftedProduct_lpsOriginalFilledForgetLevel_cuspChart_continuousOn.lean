-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_cuspChart_continuousOn
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cuspChart_continuousOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:21:16.480044+00:00
-- url     : https://prove2.me/theorems/4ed06261-d830-43eb-8c13-a9b87ce73dc4
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level cusp Chart continuous On
-- statement:
--   The true preferred cusp parametrization followed by the level map is continuous on the full disc.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L278-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L278-L302

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_cuspChart_continuousOn
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    ContinuousOn
      (fun q : ℂ => lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledCuspChart M c).symm q))
      (lpsOriginalFilledCuspChart M c).target := by sorry
