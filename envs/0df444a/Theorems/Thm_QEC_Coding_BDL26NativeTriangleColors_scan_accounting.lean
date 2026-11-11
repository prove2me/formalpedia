-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_scan_accounting
-- name    : QEC.Coding.BDL26NativeTriangleColors.scan_accounting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:51:17.042207+00:00
-- url     : https://prove2.me/theorems/42b76a86-6002-4fa1-a9aa-35527072e9f3
-- title:
--   BDL26 Native Triangle Colors: scan accounting
-- statement:
--   Exact rejected/accepted accounting, including empty return and missing row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L158-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L158-L171

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.scan_accounting {A : Type*} [DecidableEq A] (k : ℕ) (a : A) (i : Fin 3)
    (r : AtlasRow A) (L : List (AtlasRow A)) :
    (fiberScanQ k a i (r::L)).operations=(fiberScanQ k a i L).operations+
      (match r.2 with | none => 8 | some _ => 17+(if hit k a i r then 1 else 0)) ∧
    (fiberScanQ k a i (r::L)).allocations=(fiberScanQ k a i L).allocations := by sorry
