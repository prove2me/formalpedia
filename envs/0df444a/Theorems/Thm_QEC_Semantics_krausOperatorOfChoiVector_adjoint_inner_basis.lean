-- Prove2me | Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_adjoint_inner_basis
-- name    : QEC.Semantics.krausOperatorOfChoiVector_adjoint_inner_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:33:05.725256+00:00
-- url     : https://prove2.me/theorems/8bd1411e-7b7d-44e4-916b-f3a78d7b5ef4
-- title:
--   Semantics: kraus Operator Of Choi Vector adjoint inner basis
-- statement:
--   The Semantics construction uses the kraus Operator Of Choi Vector adjoint inner basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L70-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L70-L79

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

theorem QEC.Semantics.krausOperatorOfChoiVector_adjoint_inner_basis {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex (bH i)
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p)) =
      v (i, p) := by sorry
