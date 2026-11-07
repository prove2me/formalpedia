-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_stabilizer_none
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_stabilizer_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:16:27.367316+00:00
-- url     : https://prove2.me/theorems/62d5c90d-dc5e-4d9e-b527-f906639c0e6c
-- title:
--   Tanner Lifted Product: lps Hecke Index stabilizer none
-- statement:
--   The genuine finite-action infinity stabilizer is the actual relative Gamma0(Np) subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L87-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L87-L96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_stabilizer_none (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) (none:Option (Fin p)) =
      (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N) := by sorry
