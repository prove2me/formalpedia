-- Prove2me | Theorems.Thm_QEC_Semantics_lindbladDissipator_good_input_right
-- name    : QEC.Semantics.lindbladDissipator_good_input_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:25:41.399944+00:00
-- url     : https://prove2.me/theorems/8837f6df-e2a8-41f1-8d4c-398ea3704fb0
-- title:
--   Semantics: lindblad Dissipator good input right
-- statement:
--   The Semantics construction uses the lindblad Dissipator good input right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L332-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L332-L343

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.lindbladDissipator_good_input_right [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hPA : Commute P A) (hOA : Commute O A) :
    (1 - P) * lindbladDissipator J (O * P * A) =
      (1 - P) * lindbladDissipator J (P * A) * O := by sorry
