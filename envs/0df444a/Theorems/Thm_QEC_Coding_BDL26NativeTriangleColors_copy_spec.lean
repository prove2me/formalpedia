-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_copy_spec
-- name    : QEC.Coding.BDL26NativeTriangleColors.copy_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:15:46.679076+00:00
-- url     : https://prove2.me/theorems/0923d347-184a-451c-9d83-71fbd704cbcb
-- title:
--   BDL26 Native Triangle Colors: copy spec
-- statement:
--   The BDL26 Native Triangle Colors construction uses the copy spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L113-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L113-L115

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.copy_spec (c : Code) :
    (copyCodeQ c).value=c ∧ (copyCodeQ c).operations=21 ∧ (copyCodeQ c).allocations=1 := by sorry
