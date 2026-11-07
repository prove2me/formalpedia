-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_some_zero_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_some_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:50.93925+00:00
-- url     : https://prove2.me/theorems/2b2ac311-4321-472f-b361-26703afa79c3
-- title:
--   Tanner Lifted Product: lps Hecke Right Index some zero iff
-- statement:
--   The zero finite index is fixed exactly by the genuine second intersection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L115-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L115-L128

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_some_zero_iff (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    lpsHeckeRightIndex N p hNp γ hγ (some ⟨0,(Fact.out:p.Prime).pos⟩)=
        some ⟨0,(Fact.out:p.Prime).pos⟩ ↔
      γ ∈ lpsHeckeConjugateIntersection N p := by sorry
