-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_nodup
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keySetup_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:30:54.41735+00:00
-- url     : https://prove2.me/theorems/fc89ddb7-864b-4496-89f8-9fedf5a0e45f
-- title:
--   BDL26 Native Triangle Keys: key Setup nodup
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Setup nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L240-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L240-L244

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.keySetup_nodup (S : OddScale) (n : ℕ) :
    (keySetupQ S n).1.Nodup ∧ ((keySetupQ S n).1.map Prod.snd).Nodup := by sorry
