-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_interactionGraph_adj_iff
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.interactionGraph_adj_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:26.539358+00:00
-- url     : https://prove2.me/theorems/8907724e-4824-45fc-bc75-6ad3de8f3e00
-- title:
--   Local Stabilizer Hamiltonian: interaction Graph adj iff
-- statement:
--   Interaction-graph adjacency is common support in one selected term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L89-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L89-L94

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.interactionGraph_adj_iff
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (p q : ι) :
    H.interactionGraph.adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ H.generatorSupport j ∧ q ∈ H.generatorSupport j := by sorry
