-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_symmetric
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:22.166382+00:00
-- url     : https://prove2.me/theorems/144bdab0-50fd-4b94-965e-d8ecf82dff9c
-- title:
--   Binary Stabilizer Presentation: fixed Generator Interaction Graph symmetric
-- statement:
--   The fixed-generator interaction graph is symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L91-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L91-L95

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_symmetric
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) {p q : ι}
    (h : P.fixedGeneratorInteractionGraph.adjacent p q) :
    P.fixedGeneratorInteractionGraph.adjacent q p := by sorry
