-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorNoCrossEdge_iff_no_cross_interaction
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorNoCrossEdge_iff_no_cross_interaction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:37.218984+00:00
-- url     : https://prove2.me/theorems/bc8d0ca0-85eb-47ed-9b86-59042142f519
-- title:
--   Binary Stabilizer Presentation: fixed Generator No Cross Edge iff no cross interaction
-- statement:
--   The fixed interaction graph has no cross-edge exactly when no selected generator
--   has actual Pauli support on distinct vertices across the two regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L169-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L169-L183

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorNoCrossEdge_iff_no_cross_interaction
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) :
    P.fixedGeneratorNoCrossEdge A B ↔
      ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B → p ≠ q →
        ∀ j : κ,
          ¬ (p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by sorry
