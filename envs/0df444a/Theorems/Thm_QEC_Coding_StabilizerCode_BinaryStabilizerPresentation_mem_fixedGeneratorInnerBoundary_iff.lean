-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_fixedGeneratorInnerBoundary_iff
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorInnerBoundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:45:16.54278+00:00
-- url     : https://prove2.me/theorems/a9642a31-3dcd-4d5f-8d0f-0a85b749e58c
-- title:
--   Binary Stabilizer Presentation: mem fixed Generator Inner Boundary iff
-- statement:
--   Graph-level characterization of fixed-generator inner-boundary membership.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L137-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L137-L141

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorInnerBoundary_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (p : ι) :
    p ∈ P.fixedGeneratorInnerBoundary A ↔
      p ∈ A ∧ ∃ q : ι, q ∉ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q := by sorry
