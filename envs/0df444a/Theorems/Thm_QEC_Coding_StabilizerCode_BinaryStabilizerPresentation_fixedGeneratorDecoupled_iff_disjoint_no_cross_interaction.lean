-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:07:50.66545+00:00
-- url     : https://prove2.me/theorems/17e9b71f-b5a7-454f-b524-0b33e4fe435b
-- title:
--   Binary Stabilizer Presentation: fixed Generator Decoupled iff disjoint no cross interaction
-- statement:
--   Fixed-generator decoupling holds exactly when the regions are disjoint and no
--   selected generator has actual Pauli support in both regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L197-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FixedGeneratorInteraction.lean#L197-L218

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) :
    P.fixedGeneratorDecoupled A B ↔
      Disjoint A B ∧ ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B →
        ∀ j : κ,
          ¬ (p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by sorry
