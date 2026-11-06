-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_extendedMinimumDistance_eq_top_iff
-- name    : QEC.Coding.HypergraphProduct.extendedMinimumDistance_eq_top_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:52:57.846215+00:00
-- url     : https://prove2.me/theorems/98afd2be-acf1-488f-9a80-c7b2667eb595
-- title:
--   Hypergraph Product: extended Minimum Distance eq top iff
-- statement:
--   A classical code has infinite extended distance exactly when it is the
--   zero code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance.lean#L73-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance.lean#L73-L90

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.extendedMinimumDistance_eq_top_iff
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (C : LinearCode F iota) :
    extendedMinimumDistance C = ⊤ ↔ C.carrier = ⊥ := by sorry
