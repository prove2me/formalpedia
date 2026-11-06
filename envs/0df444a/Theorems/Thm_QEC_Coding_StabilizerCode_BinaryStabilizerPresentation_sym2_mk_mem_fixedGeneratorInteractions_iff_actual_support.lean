-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:46:46.904176+00:00
-- url     : https://prove2.me/theorems/9eabfa20-4a08-430e-b777-260da8391657
-- title:
--   Binary Stabilizer Presentation: sym2 mk mem fixed Generator Interactions iff actual support
-- statement:
--   An unordered pair is present exactly when one selected generator supports both endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L102-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L102-L109

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    s(p, q) ∈ P.fixedGeneratorInteractions ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by sorry
