-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_boundary2_basis_le
-- name    : QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_boundary2_basis_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:07:16.249205+00:00
-- url     : https://prove2.me/theorems/af62b294-640d-422b-8f0c-068f99a42808
-- title:
--   Cyclic Locality: Hamming Weight boundary2 basis le
-- statement:
--   A degree-two lifted-product check row consists of one column of the
--   cyclic `1+x` boundary and one ordinary Tanner basis column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L244-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L244-L313

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v

theorem QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_boundary2_basis_le
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {tannerBound : Nat}
    (hTanner : ∀ i : aCol × G,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ tannerBound)
    (c2 : LiftedProduct.C2Index aCol Unit G) :
    HammingWeight
        (LiftedProduct.boundary2 (Cyclic.liftedProductData A x)
          (canonicalBasisWord (F := ZMod 2) c2)) ≤
      tannerBound + 2 := by sorry
