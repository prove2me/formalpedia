-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_generatedVectorSubspace_eq_span_generators
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.generatedVectorSubspace_eq_span_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:16.174207+00:00
-- url     : https://prove2.me/theorems/d3df1fdb-bd57-4715-b8ac-c420bd5a4574
-- title:
--   Binary Stabilizer Presentation: generated Vector Subspace eq span generators
-- statement:
--   The real generated vector subspace is the span of the fixed generator vectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L94-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L94-L117

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.generatedVectorSubspace_eq_span_generators
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.code.1.generatedVectorSubspace =
      Submodule.span (ZMod 2) (Set.range (fun j => (P.generators j).vector)) := by sorry
