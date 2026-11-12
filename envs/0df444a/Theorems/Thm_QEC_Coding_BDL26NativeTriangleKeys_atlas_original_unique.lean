-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_atlas_original_unique
-- name    : QEC.Coding.BDL26NativeTriangleKeys.atlas_original_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:33:17.377919+00:00
-- url     : https://prove2.me/theorems/40a44c3a-98fb-4aef-a023-3fff7e258ae3
-- title:
--   BDL26 Native Triangle Keys: atlas original unique
-- statement:
--   The BDL26 Native Triangle Keys construction uses the atlas original unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L350-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L350-L365

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.atlas_original_unique (S : OddScale) (n : ℕ) (k : Fin (triangleCount S n)) :
    ∃!t : Triangle (P S n),(encode S n t,k.val)∈(keySetupQ S n).1 := by sorry
