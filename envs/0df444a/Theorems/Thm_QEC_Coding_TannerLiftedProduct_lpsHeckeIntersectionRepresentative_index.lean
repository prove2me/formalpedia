-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionRepresentative_index
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionRepresentative_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:59:31.369086+00:00
-- url     : https://prove2.me/theorems/674feedb-f008-4725-abbe-e06c82b19791
-- title:
--   Tanner Lifted Product: lps Hecke Intersection Representative index
-- statement:
--   The inverse of each genuine original first representative has its exact Hecke index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L54-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L54-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionRepresentative_index (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (lpsHeckeIntersectionRepresentative N p hNp i:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem
        (lpsHeckeIntersectionRepresentative N p hNp i).property) none=i := by sorry
