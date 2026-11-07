-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_HammingWeight_boundary_columns_basis_le
-- name    : QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_boundary_columns_basis_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:07:15.812227+00:00
-- url     : https://prove2.me/theorems/1e237b36-1892-421d-a780-f23cd3a75008
-- title:
--   Cyclic Locality: Hamming Weight boundary columns basis le
-- statement:
--   For either type of lifted-product qubit, its two boundary columns have
--   combined weight at most the larger Tanner bound plus the cyclic contribution
--   two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L318-L469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L318-L469

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v

theorem QEC.Coding.BalancedProduct.CyclicLocality.HammingWeight_boundary_columns_basis_le
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    {forwardBound transposeBound : Nat}
    (hForward : ∀ i : aCol × G,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ forwardBound)
    (hTranspose : ∀ i : aRow × G,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤
          transposeBound)
    (q : LiftedProduct.QubitIndex aRow aCol Unit Unit G) :
    HammingWeight
        (LiftedProduct.boundary1 (Cyclic.liftedProductData A x)
          (canonicalBasisWord (F := ZMod 2) q)) +
      HammingWeight
        (wordLinearMapTranspose
          (LiftedProduct.boundary2 (Cyclic.liftedProductData A x))
          (canonicalBasisWord (F := ZMod 2) q)) ≤
      max forwardBound transposeBound + 2 := by sorry
