-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_value
-- name    : QEC.Coding.BDL26NativeTriangleColors.colors_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:29:38.291934+00:00
-- url     : https://prove2.me/theorems/a891882e-5ab3-43f0-8074-e5d8fbb99963
-- title:
--   BDL26 Native Triangle Colors: colors value
-- statement:
--   The BDL26 Native Triangle Colors construction uses the colors value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L288-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L288-L294

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.colors_value (S : OddScale) (n : ℕ) :
    (colorsQ S n).value=(T S n).map
      (fun c => (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value c).value) := by sorry
