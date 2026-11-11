-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keySetup_spec
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keySetup_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:48:32.927166+00:00
-- url     : https://prove2.me/theorems/cbb0ec2e-4efd-4bf1-b00e-35606348fee9
-- title:
--   BDL26 Native Triangle Keys: key Setup spec
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Setup spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L223-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L223-L230

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.keySetup_spec (S : OddScale) (n : ℕ) :
    (keySetupQ S n).1=(BDL26NativePresentationGenerator.setupQ S n).1.triangles.map
        (fun c => (c,2*c.owner+c.copy)) ∧
      operations (keySetupQ S n)=(BDL26NativePresentationGenerator.setupQ S n).2+10*triangleCount S n+3 ∧
      allocations (keySetupQ S n)=BDL26NativePresentationGenerator.allocatedRecords S n+2*triangleCount S n+1 := by sorry
