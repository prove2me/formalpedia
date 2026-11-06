-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInducedSubgraph_adj_iff_actual_support
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInducedSubgraph_adj_iff_actual_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:07:56.841066+00:00
-- url     : https://prove2.me/theorems/a52ddbba-7a83-4a3c-9d9a-461c0301d15d
-- title:
--   Binary Stabilizer Presentation: fixed Generator Induced Subgraph adj iff actual support
-- statement:
--   Induced adjacency retains the actual selected-generator support characterization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L216-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L216-L222

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorInducedSubgraph_adj_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (vertices : Finset ι)
    (p q : {i : ι // i ∈ vertices}) :
    (P.fixedGeneratorInducedSubgraph vertices).adjacent p q ↔
      p.1 ≠ q.1 ∧ ∃ j : κ,
        p.1 ∈ support (P.generators j) ∧ q.1 ∈ support (P.generators j) := by sorry
