-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_quotientBoundary_starTranspose_single
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.quotientBoundary_starTranspose_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:27:45.6176+00:00
-- url     : https://prove2.me/theorems/e9e3104d-0485-4d8e-bef0-ae341cc19595
-- title:
--   BE20 Balanced: quotient Boundary star Transpose single
-- statement:
--   The BE20 Balanced construction uses the quotient Boundary star Transpose single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L64-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L64-L82

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.quotientBoundary_starTranspose_single
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (r : aRow) :
    HorizontalSubsystem.quotientBoundary (LiftedProduct.starTranspose A)
        (Pi.single r 1) =
      wordLinearMapTranspose (HorizontalSubsystem.quotientBoundary A)
        (Pi.single r 1) := by sorry
