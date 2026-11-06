-- Prove2me | Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_toMatrix
-- name    : QEC.Semantics.krausOperatorOfChoiVector_toMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:12:44.397013+00:00
-- url     : https://prove2.me/theorems/fd145be5-38dd-4f56-8b83-aa3946d9f3b4
-- title:
--   Semantics: kraus Operator Of Choi Vector to Matrix
-- statement:
--   The Semantics construction uses the kraus Operator Of Choi Vector to Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L38-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L38-L46

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.krausOperatorOfChoiVector_toMatrix {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) :
    LinearMap.toMatrix bH.toBasis bK.toBasis (krausOperatorOfChoiVector bH bK v) =
      fun p i => star (v (i, p)) := by sorry
