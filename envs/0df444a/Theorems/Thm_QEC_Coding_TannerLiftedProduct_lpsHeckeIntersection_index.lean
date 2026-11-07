-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_index
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:58.497954+00:00
-- url     : https://prove2.me/theorems/fa7818df-a623-44eb-b31d-77dd7430ec04
-- title:
--   Tanner Lifted Product: lps Hecke Intersection index
-- statement:
--   The exact original relative Gamma0(Np) index is p+1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L28-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L28-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_index (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    ((CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N)).index=p+1 := by sorry
