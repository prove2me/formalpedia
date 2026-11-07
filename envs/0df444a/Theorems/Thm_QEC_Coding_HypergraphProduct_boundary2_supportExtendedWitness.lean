-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary2_supportExtendedWitness
-- name    : QEC.Coding.HypergraphProduct.boundary2_supportExtendedWitness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:27.684662+00:00
-- url     : https://prove2.me/theorems/62c2fe8b-6362-4055-a9d6-48bc186206ed
-- title:
--   Hypergraph Product: boundary2 support Extended Witness
-- statement:
--   A restricted second-boundary equality extends to the corresponding
--   original second-boundary equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L141-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L141-L224

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.boundary2_supportExtendedWitness
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (w : Word (ZMod 2)
      (C2Index {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z}))
    (hw : boundary2 (supportRestrictedData D z) w =
      supportRestrictedWord z) :
    boundary2 D (supportExtendedWitness z w) = z := by sorry
