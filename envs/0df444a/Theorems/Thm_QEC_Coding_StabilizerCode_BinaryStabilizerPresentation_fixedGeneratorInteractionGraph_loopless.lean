-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_loopless
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_loopless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:48.571045+00:00
-- url     : https://prove2.me/theorems/4cd8684e-634f-412f-bb82-f426fb243b31
-- title:
--   Binary Stabilizer Presentation: fixed Generator Interaction Graph loopless
-- statement:
--   The fixed-generator interaction graph has no loops.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L98-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L98-L101

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_loopless
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p : ι) :
    ¬ P.fixedGeneratorInteractionGraph.adjacent p p := by sorry
