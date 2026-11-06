-- Prove2me | Theorems.Thm_QEC_Semantics_clbtGeneratorBlockOne_eq_negative_tail
-- name    : QEC.Semantics.clbtGeneratorBlockOne_eq_negative_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:44.66858+00:00
-- url     : https://prove2.me/theorems/2d2c0f19-b1a2-4d19-9bf0-26fb2a447c73
-- title:
--   Semantics: clbt Generator Block One eq negative tail
-- statement:
--   CLBT's first good-input block is rewritten onto the Gibbs tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L436-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L436-L446

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.clbtGeneratorBlockOne_eq_negative_tail [Fintype ι]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hstationary : lindbladDissipator J rho.toOperator = 0) :
    clbtGeneratorBlockOne (lindbladDissipator J) O P rho.toOperator =
      -(O * P * lindbladDissipator J ((1 - P) * rho.toOperator)) := by sorry
