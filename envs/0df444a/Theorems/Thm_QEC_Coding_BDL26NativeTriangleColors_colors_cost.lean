-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_cost
-- name    : QEC.Coding.BDL26NativeTriangleColors.colors_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:53:45.836822+00:00
-- url     : https://prove2.me/theorems/89d1f264-a6e1-4816-a456-6e859291aed3
-- title:
--   BDL26 Native Triangle Colors: colors cost
-- statement:
--   The BDL26 Native Triangle Colors construction uses the colors cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L317-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L317-L327

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.colors_cost (S : OddScale) (n : ℕ) :
    (colorsQ S n).operations≤(BDL26NativePresentationGenerator.setupQ S n).2+
      (T S n).length*(141*(T S n).length+2*(F S n).faces.length+132*(V S n).length+103)+4 ∧
    (colorsQ S n).allocations≤BDL26NativePresentationGenerator.allocatedRecords S n+
      (T S n).length*((T S n).length+3*(V S n).length+19)+2 := by sorry
