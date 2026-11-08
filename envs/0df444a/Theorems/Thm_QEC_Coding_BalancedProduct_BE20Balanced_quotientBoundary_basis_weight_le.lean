-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_quotientBoundary_basis_weight_le
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.quotientBoundary_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:27:18.170634+00:00
-- url     : https://prove2.me/theorems/28d85a26-0500-4031-ac66-0fb9fa1af1f8
-- title:
--   BE20 Balanced: quotient Boundary basis weight le
-- statement:
--   A basis bound for a lifted Tanner action descends to the augmented
--   quotient boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L30-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L30-L62

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.quotientBoundary_basis_weight_le
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G] [Nonempty G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (L : Nat)
    (hBasis : ∀ i : aCol × G,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ L)
    (c : aCol) :
    HammingWeight
      (HorizontalSubsystem.quotientBoundary A (Pi.single c 1)) ≤ L := by sorry
