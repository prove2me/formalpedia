-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorNoEdgeBetween_iff_actual_support
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorNoEdgeBetween_iff_actual_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:56.908177+00:00
-- url     : https://prove2.me/theorems/25587d72-643d-499a-8d0e-682a7969ca42
-- title:
--   Binary Stabilizer Presentation: fixed Generator No Edge Between iff actual support
-- statement:
--   Finite-region nonadjacency is exactly the absence of common actual support in
--   every selected generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L234-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L234-L247

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorNoEdgeBetween_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (left right : Finset ι) :
    P.fixedGeneratorNoEdgeBetween left right ↔
      ∀ ⦃p : ι⦄, p ∈ left → ∀ ⦃q : ι⦄, q ∈ right →
        ¬ (p ≠ q ∧ ∃ j : κ,
          p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by sorry
