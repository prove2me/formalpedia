-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_comm
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:33:51.711119+00:00
-- url     : https://prove2.me/theorems/653e4fb3-1c43-4664-8975-7d7ffd013a27
-- title:
--   Binary Stabilizer Presentation: sym2 mk mem fixed Generator Interactions comm
-- statement:
--   The unordered interaction representation is invariant under swapping endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L112-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L112-L115

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_comm
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    s(p, q) ∈ P.fixedGeneratorInteractions ↔ s(q, p) ∈ P.fixedGeneratorInteractions := by sorry
