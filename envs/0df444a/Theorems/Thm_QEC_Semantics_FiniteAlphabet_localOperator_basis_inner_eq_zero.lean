-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteAlphabet_localOperator_basis_inner_eq_zero
-- name    : QEC.Semantics.FiniteAlphabet.localOperator_basis_inner_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:16:08.698+00:00
-- url     : https://prove2.me/theorems/decf2ed7-e649-404d-954e-33443bd3b7be
-- title:
--   Finite Alphabet: local Operator basis inner eq zero
-- statement:
--   Identity action on the complementary factor annihilates distinct complement labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L83-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L83-L96

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.FiniteAlphabet
open scoped BigOperators TensorProduct
universe u
variable (A I : Type u) [Fintype A] [Fintype I] [DecidableEq I]
attribute [local instance] QEC.Semantics.FiniteAlphabet._p2m_local_instance_ac378d2a8a_23
variable {A I}

theorem QEC.Semantics.FiniteAlphabet.localOperator_basis_inner_eq_zero
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (x y : I → A) (h : ∃ j, j ∉ S.selected ∧ x j ≠ y j) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) = 0 := by sorry
