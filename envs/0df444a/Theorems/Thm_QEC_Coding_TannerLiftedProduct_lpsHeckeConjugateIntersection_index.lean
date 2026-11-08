-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_index
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:32.473411+00:00
-- url     : https://prove2.me/theorems/e70fee70-2ddb-4b08-ba3f-fe27315bf0f5
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Intersection index
-- statement:
--   The exact relative index of the actual second intersection is p+1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L65-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L65-L70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_index (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    ((lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N)).index=p+1 := by sorry
