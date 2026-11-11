-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_lookup_after_rejections
-- name    : QEC.Coding.BDL26NativeTriangleKeys.lookup_after_rejections
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:29:37.316195+00:00
-- url     : https://prove2.me/theorems/ef128b6f-616d-4058-935f-14c2c10ff1eb
-- title:
--   BDL26 Native Triangle Keys: lookup after rejections
-- statement:
--   The BDL26 Native Triangle Keys construction uses the lookup after rejections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L132-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L132-L141

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.lookup_after_rejections (c : Code) (rejected : List KeyRow) (k : ℕ)
    (tail : List KeyRow) (h : ∀r∈rejected,r.1≠c) :
    lookupRowsQ c (rejected++(c,k)::tail)=(some k,43*(rejected.length+1),1) := by sorry
