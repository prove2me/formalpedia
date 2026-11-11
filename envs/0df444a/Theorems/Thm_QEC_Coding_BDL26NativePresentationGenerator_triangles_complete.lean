-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangles_complete
-- name    : QEC.Coding.BDL26NativePresentationGenerator.triangles_complete
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:50:49.94162+00:00
-- url     : https://prove2.me/theorems/bc7a4beb-3d6a-48aa-a603-7fb15df0a4f9
-- title:
--   BDL26 Native Presentation Generator: triangles complete
-- statement:
--   Every actual face-copy pair occurs separately even if its geometric image repeats.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3605-L3609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3605-L3609

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation

theorem QEC.Coding.BDL26NativePresentationGenerator.triangles_complete (S : OddScale) (n : ℕ) (f : (state S n).presentation.Face) (d : Two) :
    {family:=3,owner:=((generatedRefines S n).fIndex f).val,copy:=d.val}∈
      (setupQ S n).1.triangles := by sorry
