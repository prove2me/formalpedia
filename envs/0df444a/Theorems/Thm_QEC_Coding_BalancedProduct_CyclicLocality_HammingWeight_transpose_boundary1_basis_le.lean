-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_transpose_boundary1_basis_le
-- name    : QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_transpose_boundary1_basis_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:07:03.195501+00:00
-- url     : https://prove2.me/theorems/5aab8a07-df18-420f-97d0-7a3d9711a7cd
-- title:
--   Cyclic Locality: Hamming Weight transpose boundary1 basis le
-- statement:
--   A degree-zero lifted-product check row consists of one star-transposed
--   Tanner basis column and one row of the cyclic `1+x` boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L170-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L170-L240

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v

theorem QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_transpose_boundary1_basis_le
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {tannerBound : Nat}
    (hTanner : ∀ i : aRow × G,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤
          tannerBound)
    (c0 : LiftedProduct.C0Index aRow Unit G) :
    HammingWeight
        (wordLinearMapTranspose
          (LiftedProduct.boundary1 (Cyclic.liftedProductData A x))
          (canonicalBasisWord (F := ZMod 2) c0)) ≤
      tannerBound + 2 := by sorry
