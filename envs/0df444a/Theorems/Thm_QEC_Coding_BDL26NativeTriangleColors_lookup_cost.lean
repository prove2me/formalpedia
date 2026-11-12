-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_cost
-- name    : QEC.Coding.BDL26NativeTriangleColors.lookup_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:56:37.972202+00:00
-- url     : https://prove2.me/theorems/b45649fa-eb59-4976-89f3-efdd29b781c5
-- title:
--   BDL26 Native Triangle Colors: lookup cost
-- statement:
--   The BDL26 Native Triangle Colors construction uses the lookup cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L575-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L575-L582

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_lookup_cost

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeTriangleColors.lookup_cost (S : OddScale) (n : ℕ) (c : Code) :
    (colorOfCodeQ S n c).operations≤(colorsQ S n).operations+43*(T S n).length+3 ∧
      (colorOfCodeQ S n c).allocations=(colorsQ S n).allocations := by sorry
