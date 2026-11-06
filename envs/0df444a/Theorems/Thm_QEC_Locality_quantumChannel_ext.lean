-- Prove2me | Theorems.Thm_QEC_Locality_quantumChannel_ext
-- name    : QEC.Locality.quantumChannel_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:37:47.413064+00:00
-- url     : https://prove2.me/theorems/9dea3773-7e1c-429e-94b6-260b2cbf92e9
-- title:
--   Locality: quantum Channel ext
-- statement:
--   The Locality construction uses the quantum Channel ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L922-L930
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L922-L930

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

theorem QEC.Locality.quantumChannel_ext {H K : Type u} [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {Phi Psi : QuantumChannel H K} (h : Phi.toLinearMap = Psi.toLinearMap) :
    Phi = Psi := by sorry
