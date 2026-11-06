-- Prove2me | Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_inner_basis
-- name    : QEC.Semantics.krausOperatorOfChoiVector_inner_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:13:10.963251+00:00
-- url     : https://prove2.me/theorems/a05a22a3-578b-4cd9-b0cc-df70d1202f74
-- title:
--   Semantics: kraus Operator Of Choi Vector inner basis
-- statement:
--   The constructed branch has the requested Choi-coordinate coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L49-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/ChoiKraus.lean#L49-L68

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

theorem QEC.Semantics.krausOperatorOfChoiVector_inner_basis {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex ((krausOperatorOfChoiVector bH bK v) (bH i)) (bK p) = v (i, p) := by sorry
