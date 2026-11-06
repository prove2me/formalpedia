-- Prove2me | Theorems.Thm_QEC_Semantics_JumpProtected_projector_mul_observable_adjoint
-- name    : QEC.Semantics.JumpProtected.projector_mul_observable_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:00:54.369757+00:00
-- url     : https://prove2.me/theorems/28812fdd-851f-4de9-94aa-bbdffb12e5eb
-- title:
--   Jump Protected: projector mul observable adjoint
-- statement:
--   Taking adjoints supplies the second protection equation used by CLBT.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L155-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L155-L168

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.JumpProtected.projector_mul_observable_adjoint [Fintype ι]
    {J : ι → Operator H} {O P : Operator H} (h : JumpProtected J O P)
    (hO : O.IsSymmetric) (hP : IsStarProjection P) (a : ι) :
    P * O * LinearMap.adjoint (J a) =
      P * LinearMap.adjoint (J a) * O := by sorry
