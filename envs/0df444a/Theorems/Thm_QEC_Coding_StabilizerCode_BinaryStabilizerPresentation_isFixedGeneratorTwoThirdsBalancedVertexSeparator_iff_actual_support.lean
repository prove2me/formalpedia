-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_isFixedGeneratorTwoThirdsBalancedVertexSeparator_iff_actual_support
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.isFixedGeneratorTwoThirdsBalancedVertexSeparator_iff_actual_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:08:33.179089+00:00
-- url     : https://prove2.me/theorems/7fa0868f-93b0-4a7f-92d4-dd024d7c2c8f
-- title:
--   Binary Stabilizer Presentation: is Fixed Generator Two Thirds Balanced Vertex Separator iff actual support
-- statement:
--   The fixed-generator `2/3` separator predicate is exactly a finite
--   partition-after-deletion with no common actual generator support across the
--   two retained regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L260-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L260-L279

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.isFixedGeneratorTwoThirdsBalancedVertexSeparator_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices separator : Finset ι) :
    P.IsFixedGeneratorTwoThirdsBalancedVertexSeparator vertices separator ↔
      ∃ left right : Finset ι,
        separator ⊆ vertices ∧
          left ∪ right = vertices \ separator ∧
          Disjoint left right ∧
          3 * left.card ≤ 2 * vertices.card ∧
          3 * right.card ≤ 2 * vertices.card ∧
          ∀ ⦃p : ι⦄, p ∈ left → ∀ ⦃q : ι⦄, q ∈ right →
            ¬ (p ≠ q ∧ ∃ j : κ,
              p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by sorry
