-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteAlphabet_localOperator_basis_diagonal_eq
-- name    : QEC.Semantics.FiniteAlphabet.localOperator_basis_diagonal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:16:03.823595+00:00
-- url     : https://prove2.me/theorems/1844bafc-42ce-43ae-a53c-45e1243944c5
-- title:
--   Finite Alphabet: local Operator basis diagonal eq
-- statement:
--   A local diagonal expectation depends only on the selected alphabet coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L99-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L99-L112

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

theorem QEC.Semantics.FiniteAlphabet.localOperator_basis_diagonal_eq
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (x y : I → A) (h : ∀ j, j ∈ S.selected → x j = y j) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex x)) =
    inner Complex (EuclideanSpace.basisFun (I → A) Complex y)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) := by sorry
