-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_scan_actual
-- name    : QEC.Coding.BDL26NativeTriangleColors.scan_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:31:21.276192+00:00
-- url     : https://prove2.me/theorems/ba1eb75c-c217-40be-9815-551176b291bc
-- title:
--   BDL26 Native Triangle Colors: scan actual
-- statement:
--   All actual atlas rows contribute exactly their original earlier-fiber
--   predicate. No generator failure is filtered away in this correspondence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L454-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L454-L490

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeTriangleColors.scan_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    (fiberScanQ (nativeKey S n t) (tripleAt (corners S n t) i) i
      (BDL26NativeSupportMetadata.atlasQ S n).value).value=nativeColor S n t i := by sorry
