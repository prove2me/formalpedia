-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_diagonalDensity_charpoly
-- name    : QEC.Semantics.DensityOperator.diagonalDensity_charpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:30.596203+00:00
-- url     : https://prove2.me/theorems/5c35d283-7d19-47bc-ba2f-3976f28e8c4b
-- title:
--   Density Operator: diagonal Density charpoly
-- statement:
--   The Density Operator construction uses the diagonal Density charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L182-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean#L182-L190

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.diagonalDensity_charpoly (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).toOperator.charpoly =
      (Matrix.diagonal fun i => (p i : Complex)).charpoly := by sorry
