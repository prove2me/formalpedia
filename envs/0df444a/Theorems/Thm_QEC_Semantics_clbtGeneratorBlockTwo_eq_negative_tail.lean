-- Prove2me | Theorems.Thm_QEC_Semantics_clbtGeneratorBlockTwo_eq_negative_tail
-- name    : QEC.Semantics.clbtGeneratorBlockTwo_eq_negative_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:54.383683+00:00
-- url     : https://prove2.me/theorems/06144818-c566-4c40-a39b-48770d13bb1f
-- title:
--   Semantics: clbt Generator Block Two eq negative tail
-- statement:
--   CLBT's second good-input block is rewritten onto the Gibbs tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L449-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L449-L461

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.clbtGeneratorBlockTwo_eq_negative_tail [Fintype ι]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hOrho : Commute O rho.toOperator) (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0) :
    clbtGeneratorBlockTwo (lindbladDissipator J) O P rho.toOperator =
      -((1 - P) * lindbladDissipator J ((1 - P) * rho.toOperator) * O) := by sorry
