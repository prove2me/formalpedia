-- Prove2me | Theorems.Thm_QEC_Locality_dual_apply_sum_basis
-- name    : QEC.Locality.dual_apply_sum_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:33.146643+00:00
-- url     : https://prove2.me/theorems/a614ddac-c375-424f-97cb-725f41727da2
-- title:
--   Locality: dual apply sum basis
-- statement:
--   The Locality construction uses the dual apply sum basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L67-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L67-L78

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.dual_apply_sum_basis (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K)
    (ψ : Module.Dual Complex K) (k : K) :
    (∑ i : β, ψ (b i) * inner Complex (b i) k) = ψ k := by sorry
