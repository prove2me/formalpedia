-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_none_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:22.407733+00:00
-- url     : https://prove2.me/theorems/4806e59c-03c7-4913-91b9-59d19d13ecb4
-- title:
--   Tanner Lifted Product: lps Hecke Right Index none iff
-- statement:
--   The infinity index is fixed exactly by original Gamma0(Np).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L73-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L73-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_none_iff (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    lpsHeckeRightIndex N p hNp γ hγ none=none ↔ γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by sorry
