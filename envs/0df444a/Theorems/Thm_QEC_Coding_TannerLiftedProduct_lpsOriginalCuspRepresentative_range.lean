-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_range
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspRepresentative_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:47.94925+00:00
-- url     : https://prove2.me/theorems/b901317f-e701-45b5-b4b9-66da5e000758
-- title:
--   Tanner Lifted Product: lps Original Cusp Representative range
-- statement:
--   The selected representative preserves the actual original cusp neighborhood.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L153-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L153-L157

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspRepresentative_range (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Set.range (lpsOriginalCuspProjection N
      (lpsOriginalCuspRepresentative N (lpsOriginalCuspOrbit N ρ)))=
        Set.range (lpsOriginalCuspProjection N ρ) := by sorry
