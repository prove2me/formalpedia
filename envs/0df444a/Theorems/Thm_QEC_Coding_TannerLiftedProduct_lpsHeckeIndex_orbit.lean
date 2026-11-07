-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_orbit
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:45.069852+00:00
-- url     : https://prove2.me/theorems/0e92471b-4ef7-4d0c-85ae-cc7c374f6c8f
-- title:
--   Tanner Lifted Product: lps Hecke Index orbit
-- statement:
--   The genuine inverse-actor action is transitive from every original Hecke index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L144-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L144-L160

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_orbit (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.orbit (CongruenceSubgroup.Gamma0 N) i=Set.univ := by sorry
