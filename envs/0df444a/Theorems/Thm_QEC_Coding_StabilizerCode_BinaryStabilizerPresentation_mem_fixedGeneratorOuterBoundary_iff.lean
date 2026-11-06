-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_fixedGeneratorOuterBoundary_iff
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorOuterBoundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:30.064427+00:00
-- url     : https://prove2.me/theorems/68a21245-64ea-482d-a4bc-d84e8d261b9d
-- title:
--   Binary Stabilizer Presentation: mem fixed Generator Outer Boundary iff
-- statement:
--   Graph-level characterization of fixed-generator outer-boundary membership.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L114-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L114-L118

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorOuterBoundary_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (q : ι) :
    q ∈ P.fixedGeneratorOuterBoundary A ↔
      q ∉ A ∧ ∃ p : ι, p ∈ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q := by sorry
