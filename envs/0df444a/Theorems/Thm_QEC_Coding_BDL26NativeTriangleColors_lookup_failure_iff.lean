-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_failure_iff
-- name    : QEC.Coding.BDL26NativeTriangleColors.lookup_failure_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:56:08.206962+00:00
-- url     : https://prove2.me/theorems/9dfbad50-0ffa-42a3-b638-3ec22877798f
-- title:
--   BDL26 Native Triangle Colors: lookup failure iff
-- statement:
--   The BDL26 Native Triangle Colors construction uses the lookup failure iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L596-L605
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L596-L605

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

theorem QEC.Coding.BDL26NativeTriangleColors.lookup_failure_iff (S : OddScale) (n : ℕ) (c : Code) :
    (colorOfCodeQ S n c).value=none ↔ ¬∃t : Triangle (P S n),encode S n t=c := by sorry
