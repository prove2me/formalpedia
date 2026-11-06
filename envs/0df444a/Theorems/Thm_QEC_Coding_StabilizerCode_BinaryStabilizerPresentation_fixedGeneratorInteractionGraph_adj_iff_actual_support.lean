-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_adj_iff_actual_support
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_adj_iff_actual_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:22.601144+00:00
-- url     : https://prove2.me/theorems/64cd9910-557f-4618-b0e9-6ccadec7ec31
-- title:
--   Binary Stabilizer Presentation: fixed Generator Interaction Graph adj iff actual support
-- statement:
--   Adjacency is exactly common actual Pauli support in one selected generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L83-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L83-L88

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInteractionGraph_adj_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    P.fixedGeneratorInteractionGraph.adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by sorry
