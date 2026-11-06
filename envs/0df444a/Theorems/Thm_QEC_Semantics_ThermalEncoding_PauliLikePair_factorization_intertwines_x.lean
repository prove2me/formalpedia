-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_factorization_intertwines_x
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.factorization_intertwines_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:31.063205+00:00
-- url     : https://prove2.me/theorems/ca6a3414-3119-4768-b711-8a71392fc309
-- title:
--   Pauli Like Pair: factorization intertwines x
-- statement:
--   The Pauli Like Pair construction uses the factorization intertwines x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L594-L607
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L594-L607

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.factorization_intertwines_x
    (v : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :
    P.factorization (P.tensorPauliX v) = P.x (P.factorization v) := by sorry
