-- Prove2me | Theorems.Thm_QEC_Semantics_clbtGenerator_eq_sum_four_blocks
-- name    : QEC.Semantics.clbtGenerator_eq_sum_four_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:28.186331+00:00
-- url     : https://prove2.me/theorems/9c28f37b-08bf-4de6-bfdc-e0f6de70e035
-- title:
--   Semantics: clbt Generator eq sum four blocks
-- statement:
--   Inserting `P + (I-P) = I` at the input and output gives the four blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L187-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L187-L201

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.clbtGenerator_eq_sum_four_blocks
    (L : Superoperator H) (O P rho : Operator H) :
    L (O * rho) =
      clbtGeneratorBlockOne L O P rho +
      clbtGeneratorBlockTwo L O P rho +
      clbtGeneratorBlockThree L O P rho +
      clbtGeneratorBlockFour L O P rho := by sorry
