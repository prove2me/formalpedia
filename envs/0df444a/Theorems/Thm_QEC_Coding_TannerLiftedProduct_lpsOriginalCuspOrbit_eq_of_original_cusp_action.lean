-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspOrbit_eq_of_original_cusp_action
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspOrbit_eq_of_original_cusp_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:32.61652+00:00
-- url     : https://prove2.me/theorems/a656cd56-2aa7-4796-bfc9-62a5f77c3f58
-- title:
--   Tanner Lifted Product: lps Original Cusp Orbit eq of original cusp action
-- statement:
--   A genuine original-group cusp action identifies actual cusp-orbit labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L34-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L34-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspOrbit_eq_of_original_cusp_action (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (he : g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ' • (OnePoint.infty : OnePoint ℝ))=
      Matrix.SpecialLinearGroup.mapGL ℝ ρ • (OnePoint.infty : OnePoint ℝ)) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' := by sorry
