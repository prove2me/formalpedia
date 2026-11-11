-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_scan_cost
-- name    : QEC.Coding.BDL26NativeTriangleColors.scan_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:59:08.491568+00:00
-- url     : https://prove2.me/theorems/6c4061c8-c87e-4648-b400-4ce81d866f65
-- title:
--   BDL26 Native Triangle Colors: scan cost
-- statement:
--   The BDL26 Native Triangle Colors construction uses the scan cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L173-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L173-L183

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.scan_cost {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3)
    (L : List (AtlasRow A)) :
    (fiberScanQ k a i L).operations≤18*L.length+1 ∧
      (fiberScanQ k a i L).allocations=0 := by sorry
