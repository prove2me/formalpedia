-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_projections
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keySetup_projections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:49:40.290761+00:00
-- url     : https://prove2.me/theorems/0971b999-b115-46c2-9e79-f586327821fb
-- title:
--   BDL26 Native Triangle Keys: key Setup projections
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Setup projections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L232-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L232-L238

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.keySetup_projections (S : OddScale) (n : ℕ) :
    ((keySetupQ S n).1.map Prod.fst)=(BDL26NativePresentationGenerator.setupQ S n).1.triangles ∧
      ((keySetupQ S n).1.map Prod.snd)=List.range (triangleCount S n) := by sorry
