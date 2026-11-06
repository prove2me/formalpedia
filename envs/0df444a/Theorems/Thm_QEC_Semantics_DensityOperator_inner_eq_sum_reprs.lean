-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_inner_eq_sum_reprs
-- name    : QEC.Semantics.DensityOperator.inner_eq_sum_reprs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:16.804588+00:00
-- url     : https://prove2.me/theorems/74c0892c-777d-4c71-b246-8bf7b22b994b
-- title:
--   Density Operator: inner eq sum reprs
-- statement:
--   Parseval's finite-coordinate identity for an orthonormal basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L323-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L323-L331

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
omit [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.inner_eq_sum_reprs
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) (x y : H) :
    inner Complex x y = ∑ i, star (b.repr x i) * b.repr y i := by sorry
