-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspOrbit_eq_iff_original_action
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspOrbit_eq_iff_original_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:52.771015+00:00
-- url     : https://prove2.me/theorems/3910243e-47b8-4535-8f9a-616acd8d6736
-- title:
--   Tanner Lifted Product: lps Original Cusp Orbit eq iff original action
-- statement:
--   True cusp-orbit equality is exactly an actual original-group cusp action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L49-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L49-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspOrbit_eq_iff_original_action (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' ↔
      ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ' • (OnePoint.infty : OnePoint ℝ))=
          Matrix.SpecialLinearGroup.mapGL ℝ ρ • (OnePoint.infty : OnePoint ℝ) := by sorry
