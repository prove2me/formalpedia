-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateCosetEquiv_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCosetEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:26.019924+00:00
-- url     : https://prove2.me/theorems/49ad6cd6-1248-47ae-a168-1efbd6ef79cf
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Coset Equiv mk
-- statement:
--   The second true left-coset equivalence evaluates by the inverse actor at the zero finite index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L56-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetCover.lean#L56-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsHeckeConjugateCosetEquiv N p hNp (QuotientGroup.mk γ) =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
        ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property)
        (some ⟨0,(Fact.out:p.Prime).pos⟩) := by sorry
