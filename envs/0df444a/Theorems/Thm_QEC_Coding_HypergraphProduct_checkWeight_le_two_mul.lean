-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_checkWeight_le_two_mul
-- name    : QEC.Coding.HypergraphProduct.checkWeight_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:41:42.628245+00:00
-- url     : https://prove2.me/theorems/0d33cd4b-b139-4658-8364-775c1e7e3633
-- title:
--   Hypergraph Product: check Weight le two mul
-- statement:
--   Uniform input row/column bound implies the same uniform sum bound on all
--   output checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L351-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L351-L372

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.checkWeight_le_two_mul
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) (w : Nat)
    (hRowOne : ∀ r, rowWeight D.first r ≤ w)
    (hColOne : ∀ c, columnWeight D.first c ≤ w)
    (hRowTwo : ∀ r, rowWeight D.second r ≤ w)
    (hColTwo : ∀ c, columnWeight D.second c ≤ w) :
    (∀ x₀, HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single x₀ 1)) ≤ 2 * w) ∧
      (∀ x₂, HammingWeight (boundary2 D (Pi.single x₂ 1)) ≤ 2 * w) := by sorry
