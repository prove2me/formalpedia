-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_range
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keySetup_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:29:21.870476+00:00
-- url     : https://prove2.me/theorems/f03690d0-80d0-45d4-8c49-34d1c2bfbdab
-- title:
--   BDL26 Native Triangle Keys: key Setup range
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Setup range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L246-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L246-L248

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.keySetup_range (S : OddScale) (n : ℕ) (k : ℕ) :
    k∈((keySetupQ S n).1.map Prod.snd) ↔ k<triangleCount S n := by sorry
