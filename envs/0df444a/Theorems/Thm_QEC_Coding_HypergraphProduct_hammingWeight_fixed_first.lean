-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_fixed_first
-- name    : QEC.Coding.HypergraphProduct.hammingWeight_fixed_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:08:04.668451+00:00
-- url     : https://prove2.me/theorems/41346789-85ed-4650-9ade-148715e9e6f0
-- title:
--   Hypergraph Product: hamming Weight fixed first
-- statement:
--   The Hypergraph Product construction uses the hamming Weight fixed first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L44-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L44-L81

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.hammingWeight_fixed_first
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [DecidableEq A] [Fintype B]
    (a : A) (x : Word F B) :
    HammingWeight (fun p : A × B => if a = p.1 then x p.2 else 0) =
      HammingWeight x := by sorry
