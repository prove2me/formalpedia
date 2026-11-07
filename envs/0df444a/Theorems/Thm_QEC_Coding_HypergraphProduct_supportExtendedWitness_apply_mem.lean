-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_supportExtendedWitness_apply_mem
-- name    : QEC.Coding.HypergraphProduct.supportExtendedWitness_apply_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:37.374293+00:00
-- url     : https://prove2.me/theorems/17e7d050-51a4-4450-9876-487dd75fa81b
-- title:
--   Hypergraph Product: support Extended Witness apply mem
-- statement:
--   The Hypergraph Product construction uses the support Extended Witness apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L126-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L126-L137

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.supportExtendedWitness_apply_mem
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (w : Word (ZMod 2)
      (C2Index {c // c ∈ activeFirstColumns z}
        {r // r ∈ activeSecondRows z}))
    (c : {c // c ∈ activeFirstColumns z})
    (r : {r // r ∈ activeSecondRows z}) :
    supportExtendedWitness z w (c.1, r.1) = w (c, r) := by sorry
