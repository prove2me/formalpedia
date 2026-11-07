-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspRepresentative_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:28.355369+00:00
-- url     : https://prove2.me/theorems/dc298de1-6598-4988-8eb3-954b5cfd201e
-- title:
--   Tanner Lifted Product: lps Original Cusp Representative orbit
-- statement:
--   The selected integral representative realizes its true original cusp label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L147-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L147-L150

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspRepresentative_orbit (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    lpsOriginalCuspOrbit N (lpsOriginalCuspRepresentative N c)=c := by sorry
