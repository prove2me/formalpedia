-- Prove2me | Theorems.Thm_QEC_Semantics_lindbladDissipator_good_input_left
-- name    : QEC.Semantics.lindbladDissipator_good_input_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:29.438562+00:00
-- url     : https://prove2.me/theorems/a7c3c468-b2f0-4cce-aed7-40fccab788fa
-- title:
--   Semantics: lindblad Dissipator good input left
-- statement:
--   The Semantics construction uses the lindblad Dissipator good input left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L249-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L249-L259

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.lindbladDissipator_good_input_left [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P) :
    P * lindbladDissipator J (O * P * A) =
      O * P * lindbladDissipator J (P * A) := by sorry
