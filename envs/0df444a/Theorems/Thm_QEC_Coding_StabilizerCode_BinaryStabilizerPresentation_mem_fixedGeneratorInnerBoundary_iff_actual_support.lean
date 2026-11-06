-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_fixedGeneratorInnerBoundary_iff_actual_support
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorInnerBoundary_iff_actual_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:46:41.468742+00:00
-- url     : https://prove2.me/theorems/3002f7e4-f2cf-4cf4-8e12-d11e52f8e08e
-- title:
--   Binary Stabilizer Presentation: mem fixed Generator Inner Boundary iff actual support
-- statement:
--   Inner-boundary membership is witnessed by actual support of one fixed generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L144-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L144-L157

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_fixedGeneratorInnerBoundary_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (p : ι) :
    p ∈ P.fixedGeneratorInnerBoundary A ↔
      p ∈ A ∧ ∃ q : ι, q ∉ A ∧ p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by sorry
