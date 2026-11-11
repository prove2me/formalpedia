-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangles_injective
-- name    : QEC.Coding.BDL26NativePresentationGenerator.triangles_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:01:32.002931+00:00
-- url     : https://prove2.me/theorems/bda3142d-46f0-427a-9c3f-09422fe68f99
-- title:
--   BDL26 Native Presentation Generator: triangles injective
-- statement:
--   The BDL26 Native Presentation Generator construction uses the triangles injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3611-L3617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3611-L3617

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

theorem QEC.Coding.BDL26NativePresentationGenerator.triangles_injective (S : OddScale) (n : ℕ) :
    Function.Injective (fun a : (state S n).presentation.Face × Two =>
      ({family:=3,owner:=((generatedRefines S n).fIndex a.1).val,copy:=a.2.val} : Code)) := by sorry
