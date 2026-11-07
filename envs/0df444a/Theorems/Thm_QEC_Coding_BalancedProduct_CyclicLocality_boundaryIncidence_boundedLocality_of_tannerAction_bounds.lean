-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicLocality_boundaryIncidence_boundedLocality_of_tannerAction_bounds
-- name    : QEC.Coding.BalancedProduct.CyclicLocality.boundaryIncidence_boundedLocality_of_tannerAction_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:27:16.070631+00:00
-- url     : https://prove2.me/theorems/16b98bb7-fda4-4a40-8b15-7b50b7d3948f
-- title:
--   Cyclic Locality: boundary Incidence bounded Locality of tanner Action bounds
-- statement:
--   Tanner column bounds and the actual cyclic `1+x` matrix yield uniform
--   bounded locality for the cyclic balanced product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L473-L555
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicLocality.lean#L473-L555

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicLocality
open QEC.Coding
open PKDistance
universe u v

theorem QEC.Coding.BalancedProduct.CyclicLocality.boundaryIncidence_boundedLocality_of_tannerAction_bounds
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
          transposeBound) :
    BoundedLocality
      (LiftedProduct.boundaryIncidence
        (Cyclic.liftedProductData A x)).localityProfile
      (max forwardBound transposeBound + 2) := by sorry
