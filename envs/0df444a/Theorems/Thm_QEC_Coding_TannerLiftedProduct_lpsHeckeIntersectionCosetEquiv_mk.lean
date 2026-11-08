-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionCosetEquiv_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCosetEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:59.585218+00:00
-- url     : https://prove2.me/theorems/7e5b767d-3220-4f33-962b-fda693644804
-- title:
--   Tanner Lifted Product: lps Hecke Intersection Coset Equiv mk
-- statement:
--   The actual left-coset equivalence evaluates by the inverse right-index actor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L36-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L36-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsHeckeIntersectionCosetEquiv N p hNp (QuotientGroup.mk γ) =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
        ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property) none := by sorry
