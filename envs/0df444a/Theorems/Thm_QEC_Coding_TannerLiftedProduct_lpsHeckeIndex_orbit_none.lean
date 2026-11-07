-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_orbit_none
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_orbit_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:55.922743+00:00
-- url     : https://prove2.me/theorems/77442ae5-13b3-4b5c-976e-091f3c6464a2
-- title:
--   Tanner Lifted Product: lps Hecke Index orbit none
-- statement:
--   Every original representative index occurs in the actual infinity orbit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L99-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L99-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_orbit_none (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.orbit (CongruenceSubgroup.Gamma0 N) (none:Option (Fin p))=Set.univ := by sorry
