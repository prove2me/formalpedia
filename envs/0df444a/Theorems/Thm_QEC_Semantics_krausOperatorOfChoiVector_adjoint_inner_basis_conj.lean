-- Prove2me | Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_adjoint_inner_basis_conj
-- name    : QEC.Semantics.krausOperatorOfChoiVector_adjoint_inner_basis_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:34:17.294043+00:00
-- url     : https://prove2.me/theorems/bbe07a3f-aec5-4b70-8c7f-07534b27b8f4
-- title:
--   Semantics: kraus Operator Of Choi Vector adjoint inner basis conj
-- statement:
--   The Semantics construction uses the kraus Operator Of Choi Vector adjoint inner basis conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L81-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L81-L100

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

theorem QEC.Semantics.krausOperatorOfChoiVector_adjoint_inner_basis_conj {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))
      (bH i) =
      star (v (i, p)) := by sorry
